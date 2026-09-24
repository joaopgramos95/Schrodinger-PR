# Contributing

Contributions are welcome through focused issues and pull requests.

## Manuscript changes

- Edit the source `.tex` files, not generated PDFs or auxiliary files.
- Build the affected article with `make article` or `make stationary` before opening a pull request.
- Keep theorem statements, assumptions, and citations precise.  Include enough explanation for a mathematical referee to assess a substantive change.

## Lean workspace

The Lean sources in `SchrodingerPR_verified/` are an active formalization effort.  Before changing them, read `SchrodingerPR_verified/Lean_Code/AXIOM_STATUS.md` and `SchrodingerPR_verified/LLM_HANDOFF.md`.  Do not replace a gap with `sorry`, `admit`, or a new project axiom without documenting it.

## Commits

- Keep commits narrow and describe the user-visible change.
- Do not commit local editor files, TeX build products, or Lean build caches.
