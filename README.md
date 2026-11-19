# Soviet Science, Verified

An open dataset of Soviet mathematics and physics: **English translations** paired with
**Lean 4 formalizations** of the main results, starting with four subjects: turbulence,
probability, analysis and high-energy physics.

- **Website:** https://michalshavitnyu.github.io/soviet-science-lean
- **Dataset:** [`dataset.jsonl`](https://michalshavitnyu.github.io/soviet-science-lean/dataset.jsonl),
  one record per work, with metadata, translation, notes, Lean source and the machine-checked
  status of every formalized theorem.
- **Contribute:** see [CONTRIBUTING.md](CONTRIBUTING.md).

## How it works

```
entries/<subject>/<id>/meta.yaml   ─┐
entries/<subject>/<id>/*.md        ─┼─► scripts/catalog.py ─► _site/ (GitHub Pages)
SovietScience/**/*.lean ─► lake build ─► #print axioms ─► status.json ─┘
```

Each change runs CI: it validates the metadata, builds the Lean library against Mathlib,
classifies each listed theorem as *proved* or *statement only* from its axioms, and rebuilds
the site and dataset. A Lean level shown on the site is always the one CI computed.

## Layout

| Path | Contents |
|---|---|
| `entries/` | one folder per work, grouped by subject |
| `SovietScience/` | the Lean library (Lean `v4.35.0`, Mathlib `v4.35.0`) |
| `subjects.yaml` | the subject list |
| `scripts/catalog.py` | validation, axiom audit, site and dataset builder |
| `site/assets/` | stylesheet and catalogue filter |
| `templates/entry/` | starting point for a new entry |

## Licences

Translations and notes: CC BY 4.0. Lean code and scripts: Apache 2.0. Original texts keep
their own copyright; see each entry's `copyright` field.

Maintained by [Michal Shavit](https://michalshavitnyu.github.io).
