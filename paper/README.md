# DLC Paper Draft

LaTeX source for the DLC paper. Targets arXiv submission (cs.LO + cs.CR
cross-listing), with secondary targets POPL or CCS depending on closure
status of T1-T4 at submission time.

## Building

```
make pdf
```

Requires `latexmk` and `acmart.cls` (TeX Live `texlive-publishers` package
on Debian/Ubuntu, MacTeX on macOS).

## Status

- `main.tex` — top-level document. Uses `acmart` in `nonacm` mode for
  arXiv-compatible single-column layout.
- `sections/01-introduction.tex` — drafted; positions the chain-splicing
  contribution.
- `sections/02-calculus.tex` — drafted; presents syntax and key typing
  rules.
- `sections/03-metatheory.tex` — drafted; states T1-T4 and reports
  current mechanization status (Table 1).
- `sections/04-symbolic.tex` — drafted; covers Tamarin model + ProVerif
  cross-check + the two-modeling-gaps story.
- `sections/05-wire.tex` — drafted; wire format + content addressing +
  Tamarin/ProVerif exporters.
- `sections/06-computational.tex` — drafted; EUF-CMA reduction sketch +
  the EasyCrypt vs. VCVio routes.
- `sections/07-related.tex` — drafted; positions against AITH, LLMbda,
  NAL, Garg-Pfenning, macaroons, RFC 8693.
- `sections/08-conclusion.tex` — drafted; explicit gap statement + the
  diagonal contribution claim.
- `bib.bib` — 18 entries covering the related-work landscape.

## Length target

15-20 pages two-column ACM equivalent, or 20-25 pages single-column
arXiv layout. Currently the drafted sections compose to roughly that
target.

## What this draft is NOT

A submission-ready paper. The sections are first-draft writing; they
need (1) referee-style scrutiny on technical claims, (2) figures for the
typing rules and protocol traces, (3) tighter prose throughout, (4)
collaborator review on each axis (Pfenning/Garg on the logic, Cremers
on the Tamarin model, Blanchet on the computational sketch).

The point of having this draft on `main` is that subsequent work can
refer to specific sections, and the artifact's narrative is now
committed to a single document rather than scattered across spec files.
