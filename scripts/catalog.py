#!/usr/bin/env python3
"""Catalogue tooling: validate entries, audit Lean axioms, build the site and dataset.

    python3 scripts/catalog.py validate   # check every entries/*/*/meta.yaml
    python3 scripts/catalog.py audit      # #print axioms for every listed theorem -> status.json
    python3 scripts/catalog.py site       # build _site/ (HTML + dataset.json/.jsonl)
    python3 scripts/catalog.py all        # all three, in order

Requires: pyyaml, markdown. The audit step requires a built Lean library (`lake build`).
"""
from __future__ import annotations

import html
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
ENTRIES = ROOT / "entries"
SITE = ROOT / "_site"
STATUS = ROOT / "status.json"
CONFIG = yaml.safe_load((ROOT / "site.yaml").read_text())
SUBJECTS = yaml.safe_load((ROOT / "subjects.yaml").read_text())
SUBJECT_IDS = [s["id"] for s in SUBJECTS]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TRANSLATION_STATUSES = ["none", "partial", "complete"]
COPYRIGHT_STATUSES = ["public-domain", "permission", "in-copyright"]
REQUIRED = ["id", "subject", "title_original", "title_en", "authors", "year", "language",
            "source", "summary", "copyright", "translation", "contributors"]
ID_RE = re.compile(r"^\d{4}-[a-z0-9]+(-[a-z0-9]+)*$")


# ---------------------------------------------------------------- loading

def load_entries() -> list[dict]:
    out = []
    for meta in sorted(ENTRIES.glob("*/*/meta.yaml")):
        e = yaml.safe_load(meta.read_text()) or {}
        e["_dir"] = meta.parent
        out.append(e)
    return out


def lean_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def root_imports() -> set[str]:
    text = (ROOT / "SovietLean.lean").read_text()
    return set(re.findall(r"^(?:public )?import (\S+)", text, re.M))


# ---------------------------------------------------------------- validate

def validate() -> list[str]:
    errors: list[str] = []
    entries = load_entries()
    seen: set[str] = set()
    imports = root_imports()
    for e in entries:
        d: Path = e["_dir"]
        where = d.relative_to(ROOT)
        err = lambda msg: errors.append(f"{where}: {msg}")
        for k in REQUIRED:
            if k not in e:
                err(f"missing field `{k}`")
        if errors and errors[-1].startswith(f"{where}: missing"):
            continue
        if e["id"] != d.name:
            err(f"id `{e['id']}` must equal folder name `{d.name}`")
        if not ID_RE.match(e["id"]):
            err("id must look like `<year>-<author>-<short-title>` (lowercase, hyphens)")
        if e["id"] in seen:
            err("duplicate id")
        seen.add(e["id"])
        if e["subject"] not in SUBJECT_IDS:
            err(f"subject `{e['subject']}` not in subjects.yaml {SUBJECT_IDS}")
        if d.parent.name != e["subject"]:
            err(f"entry lives under entries/{d.parent.name}/ but subject is `{e['subject']}`")
        if not isinstance(e["authors"], list) or not e["authors"]:
            err("authors must be a non-empty list")
        if not isinstance(e["year"], int) or not 1700 <= e["year"] <= 2030:
            err("year must be an integer")
        cs = (e.get("copyright") or {}).get("status")
        if cs not in COPYRIGHT_STATUSES:
            err(f"copyright.status must be one of {COPYRIGHT_STATUSES}")
        ts = (e.get("translation") or {}).get("status")
        if ts not in TRANSLATION_STATUSES:
            err(f"translation.status must be one of {TRANSLATION_STATUSES}")
        if ts in ("partial", "complete"):
            if not (d / "translation.md").exists():
                err("translation.status is partial/complete but translation.md is missing")
            if cs == "in-copyright" and e["copyright"].get("maintainer_override") is not True:
                err("a translation of an in-copyright work needs copyright.status `permission` "
                    "(with a note naming the rights holder) — see CONTRIBUTING.md")
            if not e["translation"].get("translators"):
                err("translation.translators must list who translated")
        if (d / "original.pdf").exists() and cs != "public-domain":
            err("original.pdf may only be included for public-domain works; link to it instead")
        lean = e.get("lean")
        if lean is not None:
            mod = lean.get("module", "")
            if not lean_path(mod).exists():
                err(f"lean.module `{mod}` has no file {lean_path(mod).relative_to(ROOT)}")
            if mod not in imports:
                err(f"lean.module `{mod}` is not imported in SovietLean.lean")
            res = lean.get("results") or []
            if not res:
                err("lean.results must list at least one {label, decl}")
            for r in res:
                if not r.get("label") or not r.get("decl"):
                    err("each lean.results item needs `label` and `decl`")
        if ts == "none" and lean is None:
            err("an entry needs a translation, a Lean formalization, or both")
    return errors


# ---------------------------------------------------------------- audit

def audit() -> dict:
    """Run `#print axioms` on every listed declaration and classify it."""
    entries = load_entries()
    decls = [r["decl"] for e in entries if e.get("lean") for r in e["lean"]["results"]]
    status: dict = {"decls": {}, "entries": {}}
    if decls:
        src = "import SovietLean\n" + "".join(f"#print axioms {d}\n" for d in decls)
        probe = ROOT / "scripts" / "_audit.lean"
        probe.write_text(src)
        proc = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                              capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        if proc.returncode != 0:
            sys.exit(f"audit: Lean failed:\n{out}")
        for d in decls:
            m = re.search(rf"'{re.escape(d)}' depends on axioms: \[(.*?)\]", out, re.S)
            if m:
                axioms = {a.strip() for a in m.group(1).split(",") if a.strip()}
            elif f"'{d}' does not depend on any axioms" in out:
                axioms = set()
            else:
                sys.exit(f"audit: no axiom report for `{d}` — is the name right?\n{out}")
            extra = axioms - STANDARD_AXIOMS - {"sorryAx"}
            if extra:
                sys.exit(f"audit: `{d}` uses non-standard axioms {sorted(extra)}; not accepted")
            status["decls"][d] = {"axioms": sorted(axioms),
                                  "state": "statement" if "sorryAx" in axioms else "proved"}
    for e in entries:
        if not e.get("lean"):
            tier = "none"
        else:
            states = [status["decls"][r["decl"]]["state"] for r in e["lean"]["results"]]
            tier = ("proved" if all(s == "proved" for s in states)
                    else "partly-proved" if any(s == "proved" for s in states)
                    else "statements")
        status["entries"][e["id"]] = {"lean": tier}
    STATUS.write_text(json.dumps(status, indent=2) + "\n")
    return status


# ---------------------------------------------------------------- site

LEAN_BADGE = {"none": ("No Lean", "muted"), "statements": ("Lean: statements", "warn"),
              "partly-proved": ("Lean: partly proved", "info"), "proved": ("Lean: proved", "ok")}
TR_BADGE = {"none": ("No translation", "muted"), "partial": ("Translation: partial", "info"),
            "complete": ("Translation: complete", "ok")}

MATH_RE = re.compile(r"(\$\$.+?\$\$|\\\[.+?\\\]|\\\(.+?\\\)|(?<![\\$])\$[^$\n]+?\$)", re.S)


def md(text: str) -> str:
    """Markdown -> HTML, shielding TeX math from the Markdown parser (KaTeX renders it)."""
    import markdown
    stash: list[str] = []

    def keep(m):
        stash.append(m.group(0))
        return f"\x00{len(stash) - 1}\x00"

    body = markdown.markdown(MATH_RE.sub(keep, text), extensions=["tables", "fenced_code", "toc"])
    return re.sub(r"\x00(\d+)\x00", lambda m: html.escape(stash[int(m.group(1))]), body)


def badge(kind: tuple[str, str]) -> str:
    return f'<span class="badge {kind[1]}">{html.escape(kind[0])}</span>'


def page(title: str, body: str, depth: int = 0) -> str:
    up = "../" * depth
    repo = CONFIG["repo_url"]
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title if title.startswith(CONFIG["name"]) else title + " · " + CONFIG["name"])}</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<link rel="stylesheet" href="{up}assets/style.css">
<meta property="og:title" content="{html.escape(title)}">
<meta property="og:image" content="{CONFIG["site_url"]}/assets/banner-2000.jpg">
<meta name="twitter:card" content="summary_large_image">
</head><body>
<header class="top"><a class="brand" href="{up}index.html">{html.escape(CONFIG["name"])}</a>
<nav><a href="{up}index.html">Catalogue</a><a href="{up}contribute.html">Contribute</a>
<a href="{up}dataset.html">Dataset</a><a href="{repo}">GitHub</a></nav></header>
<main>{body}</main>
<footer>Translations and notes: CC BY 4.0 · Lean code: Apache 2.0 ·
<a href="{repo}">source</a></footer>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"
 onload="renderMathInElement(document.body,{{delimiters:[{{left:'$$',right:'$$',display:true}},
 {{left:'\\\\[',right:'\\\\]',display:true}},{{left:'$',right:'$',display:false}},
 {{left:'\\\\(',right:'\\\\)',display:false}}]}})"></script>
<script src="{up}assets/filter.js"></script>
</body></html>
"""


def lean_source_url(module: str) -> str:
    return f'{CONFIG["repo_url"]}/blob/{CONFIG["branch"]}/{module.replace(".", "/")}.lean'


def decl_statement(module: str, decl: str) -> str:
    """Pull the theorem's source text (docstring excluded) out of the Lean file."""
    text = lean_path(module).read_text()
    short = decl.split(".")[-1]
    m = re.search(rf"^(theorem|lemma|def) {re.escape(short)}\b.*?(?=:=)", text, re.S | re.M)
    return m.group(0).strip() if m else ""


def record(e: dict, status: dict) -> dict:
    """The dataset row for one entry (everything except local paths)."""
    d: Path = e["_dir"]
    row = {k: v for k, v in e.items() if not k.startswith("_")}
    row["lean_status"] = status["entries"].get(e["id"], {}).get("lean", "unaudited")
    for name in ("translation.md", "notes.md"):
        if (d / name).exists():
            row[name.split(".")[0] + "_text"] = (d / name).read_text()
    if e.get("lean"):
        mod = e["lean"]["module"]
        row["lean_source"] = lean_path(mod).read_text()
        for r in row["lean"]["results"]:
            r["statement"] = decl_statement(mod, r["decl"])
            r["state"] = status["decls"].get(r["decl"], {}).get("state", "unaudited")
    return row


def build_site() -> None:
    status = json.loads(STATUS.read_text()) if STATUS.exists() else {"decls": {}, "entries": {}}
    entries = load_entries()
    if SITE.exists():
        shutil.rmtree(SITE)
    (SITE / "e").mkdir(parents=True)
    shutil.copytree(ROOT / "site" / "assets", SITE / "assets")
    rows = [record(e, status) for e in entries]

    # catalogue
    counts = {s: sum(r["subject"] == s for r in rows) for s in SUBJECT_IDS}
    tabs = '<button class="tab on" data-subject="all">All <b>' + str(len(rows)) + "</b></button>"
    tabs += "".join(f'<button class="tab" data-subject="{s["id"]}">{html.escape(s["name"])} '
                    f'<b>{counts[s["id"]]}</b></button>' for s in SUBJECTS)
    cards = []
    for r in sorted(rows, key=lambda r: (r["year"], r["id"])):
        cards.append(f"""<a class="card" href="e/{r['id']}.html" data-subject="{r['subject']}"
 data-lean="{r['lean_status']}" data-tr="{r['translation']['status']}">
<div class="meta">{r['year']} · {html.escape(', '.join(r['authors']))} ·
{html.escape(next(s['name'] for s in SUBJECTS if s['id'] == r['subject']))}</div>
<h3>{html.escape(r['title_en'])}</h3><div class="orig">{html.escape(r['title_original'])}</div>
<p>{html.escape(r['summary'].strip())}</p>
<div class="badges">{badge(TR_BADGE[r['translation']['status']])}
{badge(LEAN_BADGE.get(r['lean_status'], ('Lean: unaudited', 'muted')))}
{'<span class="badge help">Help wanted</span>' if r.get('help_wanted') else ''}</div></a>""")
    empty = "".join(f'<div class="empty" data-subject="{s["id"]}" hidden>No {html.escape(s["name"].lower())} '
                    f'entries yet. <a href="contribute.html">Contribute the first one.</a></div>'
                    for s in SUBJECTS if not counts[s["id"]])
    blurbs = "".join(f'<li><b>{html.escape(s["name"])}</b> — {html.escape(s["blurb"])}</li>' for s in SUBJECTS)
    index = f"""<section class="hero"><h1 class="banner"><img src="assets/banner-1000.jpg"
 srcset="assets/banner-1000.jpg 1000w, assets/banner-2000.jpg 2000w"
 sizes="(max-width: 960px) 100vw, 928px" width="2000" height="667"
 alt="{html.escape(CONFIG['name'])}"></h1>
<p class="subtitle">{html.escape(CONFIG['title'])}</p>
<p>{html.escape(CONFIG['tagline'])}</p><ul class="subjects">{blurbs}</ul></section>
<div class="filters"><div class="tabs">{tabs}</div>
<label><input type="checkbox" id="only-proved"> Lean-proved only</label>
<label><input type="checkbox" id="only-tr"> Has translation</label></div>
<div class="grid">{''.join(cards)}</div>{empty}"""
    (SITE / "index.html").write_text(page(f"{CONFIG['name']} — {CONFIG['title']}", index))

    # entry pages
    for e, r in zip(entries, rows):
        parts = [f"""<p class="meta">{r['year']} · {html.escape(', '.join(r['authors']))}</p>
<h1>{html.escape(r['title_en'])}</h1><p class="orig">{html.escape(r['title_original'])}</p>
<div class="badges">{badge(TR_BADGE[r['translation']['status']])}
{badge(LEAN_BADGE.get(r['lean_status'], ('Lean: unaudited', 'muted')))}</div>
<dl><dt>Source</dt><dd>{html.escape(r['source'])}</dd>
<dt>Original language</dt><dd>{html.escape(r['language'])}</dd>
<dt>Copyright</dt><dd>{html.escape(r['copyright']['status'])}{' — ' + html.escape(r['copyright'].get('note', '')) if r['copyright'].get('note') else ''}</dd>"""]
        for t in r.get("existing_translations", []):
            parts.append(f"<dt>Existing translation</dt><dd>{html.escape(t)}</dd>")
        if r["translation"].get("translators"):
            parts.append(f"<dt>Translated by</dt><dd>{html.escape(', '.join(r['translation']['translators']))}</dd>")
        if r["translation"].get("reviewed_by"):
            parts.append(f"<dt>Reviewed by</dt><dd>{html.escape(', '.join(r['translation']['reviewed_by']))}</dd>")
        parts.append(f"<dt>Contributors</dt><dd>{html.escape(', '.join(r['contributors']))}</dd></dl>")
        parts.append(f"<p>{html.escape(r['summary'].strip())}</p>")
        if r.get("help_wanted"):
            parts.append(f'<div class="callout"><b>Help wanted.</b> {md(r["help_wanted"])}</div>')
        if r.get("lean"):
            mod = r["lean"]["module"]
            parts.append(f'<h2>Lean formalization</h2><p><a href="{lean_source_url(mod)}"><code>{mod}</code></a></p>')
            for res in r["lean"]["results"]:
                st = res["state"]
                parts.append(f"""<div class="result"><div class="rhead"><b>{html.escape(res['label'])}</b>
{badge(('proved', 'ok') if st == 'proved' else ('statement only (sorry)', 'warn') if st == 'statement' else ('unaudited', 'muted'))}</div>
<pre><code>{html.escape(res['statement'])}</code></pre></div>""")
        if r.get("translation_text"):
            parts.append(f'<h2>Translation</h2><article class="tr">{md(r["translation_text"])}</article>')
        if r.get("notes_text"):
            parts.append(f'<h2>Notes</h2><article>{md(r["notes_text"])}</article>')
        bib = (f"@misc{{{r['id'].replace('-', '_')},\n  author = {{{' and '.join(r['authors'])}}},\n"
               f"  title = {{{r['title_original']}}},\n  year = {{{r['year']}}},\n"
               f"  note = {{{r['source']} {CONFIG['name']} entry: {CONFIG['site_url']}/e/{r['id']}.html}}\n}}")
        parts.append(f"<h2>Cite</h2><pre><code>{html.escape(bib)}</code></pre>")
        parts.append(f'<p><a href="{CONFIG["repo_url"]}/tree/{CONFIG["branch"]}/entries/{r["subject"]}/{r["id"]}">'
                     "Edit this entry on GitHub</a></p>")
        (SITE / "e" / f"{r['id']}.html").write_text(page(r["title_en"], "".join(parts), depth=1))

    # contribute + dataset pages
    contrib = (ROOT / "CONTRIBUTING.md").read_text()
    (SITE / "contribute.html").write_text(page("Contribute", f"<article>{md(contrib)}</article>"))
    ds = f"""<h1>Dataset</h1><p>Every entry, with its metadata, translation, notes, Lean source,
the statement of each formalized result and its audited status (<code>proved</code> or
<code>statement</code>), is published as machine-readable files:</p>
<ul><li><a href="dataset.jsonl">dataset.jsonl</a> — one JSON object per line</li>
<li><a href="dataset.json">dataset.json</a> — the same, as one array</li></ul>
<p>{len(rows)} entries · {sum(r['lean_status'] == 'proved' for r in rows)} fully Lean-proved ·
{sum(r['translation']['status'] != 'none' for r in rows)} with translations.</p>
<p>Translations and notes are CC BY 4.0, Lean code Apache 2.0; check each row's
<code>copyright</code> field before reusing an original text.</p>"""
    (SITE / "dataset.html").write_text(page("Dataset", ds))
    (SITE / "dataset.json").write_text(json.dumps(rows, ensure_ascii=False, indent=1))
    (SITE / "dataset.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    (SITE / ".nojekyll").write_text("")


# ---------------------------------------------------------------- cli

def main() -> None:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "all"
    if cmd in ("validate", "all"):
        errs = validate()
        for e in errs:
            print("ERROR", e)
        if errs:
            sys.exit(1)
        print(f"validate: {len(load_entries())} entries OK")
    if cmd in ("audit", "all"):
        st = audit()
        for d, v in st["decls"].items():
            print(f"audit: {d}: {v['state']}")
    if cmd in ("site", "all"):
        build_site()
        print(f"site: built {SITE.relative_to(ROOT)}/")


if __name__ == "__main__":
    main()
