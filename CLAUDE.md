## Verification

- Check work with `lake build FreeQuantum` (or `lake env lean <file>` for a single file).

## Working Conventions

- Use ℂ directly as the base field; do not introduce `abbrev R := ℂ`.
- Comments state what the code is, tersely: no design history, no comparison with alternatives, no reference to downstream modules, no docstring that only restates the declaration. The module header keeps a brief design overview.

## Git

- Never make commits.
