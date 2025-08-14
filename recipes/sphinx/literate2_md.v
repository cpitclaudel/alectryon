(*|
# Explicit Markdown

Files ending in ``_md.v`` are processed as Markdown regardless of the ``DEFAULT_MARKUP`` setting:
|*)

Compute ((fun (n: nat) (opt: option nat) (eq: opt = Some n) => n)
           _ (Some 3) eq_refl).
