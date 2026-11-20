# Contributing

Each entry is one Soviet (or Russian-school) work in mathematics or physics. An entry can be
a **translation**, a **Lean formalization**, or ideally **both**. You contribute by opening a
pull request on GitHub; checks run automatically, and a maintainer reviews it before merging.

## Subjects

| Folder | Subject |
|---|---|
| `entries/turbulence/` | Turbulence: Kolmogorov–Obukhov theory, stability, wave turbulence |
| `entries/probability/` | Probability: foundations, limit theorems, processes, ergodic theory |
| `entries/analysis/` | Analysis: functional analysis, PDE, approximation and harmonic analysis |
| `entries/high-energy/` | High-energy physics: QFT, renormalization, particle and nuclear theory |

To propose a new subject, open an issue.

## What an entry looks like

```
entries/<subject>/<year>-<author>-<short-title>/
  meta.yaml          required — bibliographic data and status
  translation.md     the English translation (Markdown, math in $…$ and $$…$$)
  notes.md           translator's and formalizer's notes: terminology, errata, context
SovietLean/<Subject>/<Author><Year><Topic>.lean   the Lean formalization
```

Copy `templates/entry/` to start. The comments in `templates/entry/meta.yaml` explain each field.

## Lean levels

The site shows each entry's Lean level. **It is computed by CI, not declared by you**, by
running `#print axioms` on every theorem listed in `meta.yaml`:

| Level | Meaning |
|---|---|
| **statements** | The main results are stated in Lean; proofs may be `sorry`. |
| **partly proved** | Some listed results are proved, some are still `sorry`. |
| **proved** | Every listed result is proved, using only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). |

Any other axiom fails the check. A statement-only entry is a useful contribution: a faithful
formal statement is the hardest part to get right, and it invites others to finish the proof.
Entries marked *help wanted* have open proofs.

### Writing the Lean file

- Start the file with `module`, use `public import Mathlib…`, and put declarations after
  `@[expose] public section`.
- Put everything in `namespace SovietLean.<AuthorYear>`.
- In the module docstring, quote or paraphrase the source statement and say **how the formal
  version matches it**: which hypotheses were made explicit, what a phrase like "almost surely" or
  "the tail field" became. A reviewer checks this match, not just that the file compiles.
- If Mathlib already proves the result, it is fine to prove yours by citing it; credit the
  Mathlib authors in the docstring.
- Add your module to `SovietLean.lean`.

## Translations

- Translate from the original language (usually Russian). Keep the author's numbering of
  sections, theorems and equations so the Lean file can point to them.
- Keep the original notation. Record terminology choices and any errors you found in the
  original in `notes.md`; do not silently fix them in the translation.
- List yourself under `translation.translators`. A second reader who checks the translation
  against the original is added under `translation.reviewed_by`.

## Copyright — please read

Many Soviet works are **still under copyright**: in Russia, protection generally lasts for the
author's life plus 70 years (longer for some wartime authors), and the US restored copyright
in many foreign works in 1996. A translation is a derivative work, so it needs the rights
holder's permission unless the original is in the public domain.

Set `copyright.status` in `meta.yaml` to one of:

- `public-domain` — you have reason to think the work is free in both Russia and the US. Say why in `copyright.note`.
- `permission` — the rights holder (the author's heirs, the publisher) agreed. Name them in `copyright.note`.
- `in-copyright` — the default. **No translation and no scan** may be included. The entry can
  still carry a Lean formalization, a summary in your own words, and notes. Theorem statements
  and mathematical ideas are not copyrightable.

In exceptional cases a maintainer may publish an in-copyright translation by setting
`copyright.maintainer_override: true`. The entry stays marked `in-copyright`, its page says that
it is published without the rights holder's permission, and it is removed on request.

Only `public-domain` entries may include `original.pdf`; otherwise give a citation. CI enforces
these rules. This is not legal advice; when in doubt, ask in the pull request.

## Licences of contributions

By contributing you agree to license your translation and notes under **CC BY 4.0** and your
Lean code under **Apache 2.0** (the same as Mathlib).

## Checking locally

```bash
lake exe cache get        # download compiled Mathlib (first time only)
lake build
pip install pyyaml markdown
python3 scripts/catalog.py all     # validate, audit Lean levels, build _site/
```

Open `_site/index.html` to see your entry as it will appear.
