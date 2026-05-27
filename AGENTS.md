# Agent Notes

This repository formalizes arguments from `tex/demazure.tex`, which should be a
symlink to the current paper source. Before working on a theorem or definition,
read the relevant part of `demazure.tex` and try to follow the paper's proof
style and structure when it can be done idiomatically in Lean.

Docstrings should mention the paper when there is a clear reference. Follow the
existing format in the Lean files: a short explanatory docstring, with references
such as `*Definition 3.7 (first half).*`, `*Proposition 3.9 (part).*`, or
`*Theorem 4.4, part 2/5.*` near the end when appropriate.

When an agent writes an entire proof of a lemma, add a short by-line as the
first line of the proof block, using the actual model or agent name:

```lean
  -- Proof written by GPT 5.5.
```

Prefer the model version number when it is known, as in `GPT 5.5`, rather than
a generic agent name.

For a substantial subproof or substatement inside a longer lemma, use the same
style at the start of that local proof block. Keep these by-lines short and
factual.

New proofs should follow mathlib style and the existing style of this repository
as much as possible. Prefer local lemmas, named intermediate facts, `omega` or
`linarith` where they are already natural, and the existing API over
ad hoc rewrites.

Prioritize readability and maintainability in proofs. Use tactics that are
unlikely to be brittle when the Mathlib version is updated. Avoid raw `simp`
tactics except when closing a goal; it is preferable to use `simp only`.
A good strategy is to first write a proof with `simp`, then replace that with
`simp?` and apply the suggestion when it is reasonably small and readable.

In docstrings, LaTeX syntax mirroring the source paper is preferred over Lean
code snippets, except in cases where the Lean implementation should be
emphasized. Prefer inline math delimiters for paper notation, e.g.
`$\sigma_S$`, `$\alpha \star \beta$`, and `$b - 1 \in S$`, rather than bare
LaTeX like `\sigma_S` or code-form notation like `` `σ_S` ``. The documentation
is meant primarily as a guide for a reader of the paper.

Work in small chunks. It is often better to first write a proof skeleton with
deeper `sorry`s, then fill those `sorry`s one at a time, than to submit a large
proof all at once. This keeps the work readable and makes it easier to revise.

The author will review and revise each proof. This is another reason to work in
chunks, so that he can do so at each planning stage. Explain design decisions
briefly, and adapt if they are revised. Before continuing work on a proof in
progress, check the current file and working tree for author revisions, and take
those revisions as a signal of the author's intent.

For shell commands in this environment, prefix commands with `rtk`. After each
meaningful proof chunk, run a focused check such as:

```bash
rtk lake env lean Demazure/SlipFace.lean
```
