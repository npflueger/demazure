# demazure

This repository contains formalizations about the basic theory of the *Demazure product* on almost-sign-preserving permutations, as developed in the following paper.

N. Pflueger, [An extended Demazure product on integer permutations via min-plus matrix multiplication](https://arxiv.org/abs/2206.14227)

The code includes full formalizations of the main theorems of [An extended Demazure product](https://arxiv.org/abs/2206.14227), following the style, definitions, and proof structure closely. The repository also includes some additional results not included in that article, especially the classification of Demazure factorizations of 321-avoiding permutations (not necessarily of finite length).

[Documentation](https://npflueger.github.io/demazure/docs) for this repository is auto-generated using [doc-gen4](https://github.com/leanprover/doc-gen4). Note that documentation for all Mathlib dependencies is automatically generated along with this repo; you should select "Demazure" in the left column to find the documentation for this repository.

## Project Structure

The Lean development in `Demazure/` is organized as follows. Section numbers tell roughly where the material of that file is found in [An extended Demazure product](https://arxiv.org/abs/2206.14227). In some cases, material from one section is spread across multiple files, or not yet formalized, and some formalized theorems are not in that article.

```text
┌───────────────────────────────┐          ┌───────────────────────────────┐
│ Utils.lean                    │          │ Valley.lean                   │
│ Generic helper lemmas         │          │ Tools for tracking minima     │
│                               │          │ and argmin sets.              │
└───────────────┬───────────────┘          └───────────────┬───────────────┘
                │                                          │
                │                                          ▼
                │                          ┌───────────────┴───────────────┐
                │                          │ SlipFace.lean (§3)            │
                │                          │ Slipfaces and operations      │
                │                          │ on them.                      │
                │                          └───────────────┬───────────────┘
                │                                          │
                └──────────────────────────┬───────────────┘
                                           │
                                           ▼
                           ┌───────────────┴───────────────┐
                           │ AspPerm.lean (§2)             │
                           │ ASP permutations, inversion   │
                           │ sets, weak                    │
                           │ orders, ⋆ and ◃ predicates    │
                           └───────────────┬───────────────┘
                                           │
              ┌────────────────────────────┴────────────────────────────┐
              │                                                         │
              ▼                                                         ▼
┌───────────────────────────────┐          ┌───────────────────────────────┐
│ InvSet.lean (§2)              │          │ Submodular.lean (§4)          │
│ Abstract ASP inversion sets   │          │ Submodular slipfaces;         │
│ and reconstruction            │          │ ⋆ and ◃ on ASP.               │
└───────────────┬───────────────┘          └───────────────┬───────────────┘
                │                                          │
                └─────────────────────┬────────────────────┤
                                      │                    │
                                      ▼                    ▼
                      ┌───────────────┴───────────────┐    ┌───────────────┴───────────────┐
                      │ Avoiding321.lean              │    │ ReducedProducts.lean (§5)     │
                      │ 321-avoiding permutations     │    │ Reduced products              │
                      │ and behavior of ⋆ on them     │    │ and relations to ⋆ and ◃      │
                      └───────────────┬───────────────┘    └───────────────┬───────────────┘
                                      │                                    │
                                      ▼                                    ▼
                      ┌───────────────┴───────────────┐    ┌───────────────┴───────────────┐
                      │ Tableaux.lean                 │    │ Reduction.lean (§6)           │
                      │ Hecke                         │    │ Greedy and stingy             │
                      │ factorizations and            │    │ characterizations;            │
                      │ set-valued tableaux           │    │ reduction theorems            │
                      └───────────────────────────────┘    └───────────────┬───────────────┘
                                                                           │
                                                                           ▼
                                                           ┌───────────────┴───────────────┐
                                                           │ Transpositions.lean (§3, §8)  │
                                                           │ Adjacent transposition        │
                                                           │ formulas for product          │
                                                           │ and residual                  │
                                                           └───────────────────────────────┘
```

## Paper Coverage

The formalization mostly follows Sections 2--6 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), with some later
results and some additional material developed beyond that article. Lean statements
are often split into several lemmas rather than matching the article's statements
verbatim.

| Paper material | Main Lean files | Coverage notes |
| --- | --- | --- |
| Introduction: Theorems A, B, C and the operation `◃` | `Submodular.lean`, `Reduction.lean`, `Transpositions.lean` | The main theorem statements are formalized as component lemmas: existence and associativity of `⋆`, the min-plus formula, the greedy and stingy characterizations, the reduction theorem, and the adjacent-transposition formulas. |
| Section 2: ASP permutations, shift, inversions, weak orders, reduced products, inversion-set reconstruction | `AspPerm.lean`, `InvSet.lean` | Directly formalized, with reconstruction from inversion sets isolated in `InvSet.lean`. Some helper infrastructure for finite sets and integer counts lives in `Utils.lean`. |
| Section 3: Slipface functions and the operations `⋆`, `◃`, `▹` on slipfaces | `SlipFace.lean`, `Transpositions.lean` | Directly formalized, including duality, monotonicity, operation existence, associativity identities, witness-set reductions, and the formulas for products with non-overlapping adjacent transpositions. |
| Section 4: Submodular slipfaces and the induced operations on `AspPerm` | `Valley.lean`, `Submodular.lean` | Directly formalized. `Valley.lean` packages the rightmost-minimum argument used in the proof of closure under `⋆`; `Submodular.lean` formalizes closure under `⋆`, `◃`, and `▹`, inverse compatibility, shift formulas, and weak-order consequences. |
| Section 5: When `⋆`, `◃`, and `▹` are ordinary products | `ReducedProducts.lean` | Directly formalized, including the reduced-product criteria and the comparison between weak and strong Bruhat orders. |
| Section 6: Greediness, stinginess, and the reduction theorem | `Reduction.lean` | Directly formalized, including the two-factor reduction theorem and a list version of the many-factor reduction statement. |
| Section 7: Bounded-difference permutations and the essential set | none | Not broadly formalized here. The essential-set theory and bounded-difference criteria from this section are not currently part of the Lean development. |
| Section 8: Subgroups closed under `⋆` and `◃` | `Transpositions.lean` | Partially formalized. The adjacent-transposition computation used for symmetric and affine symmetric groups is formalized, but the downward-closed subgroup framework is not broadly formalized in this repository. |
| Additional material outside [An extended Demazure product](https://arxiv.org/abs/2206.14227) | `Avoiding321.lean`, `Tableaux.lean` | These files develop 321-avoiding ASP permutations, triangle-free inversion sets, Demazure factorization criteria, Hecke factorizations, chains of inversion boxes, and set-valued tableaux. |

## Installation

To download and build this code, follow the steps below.

1. **Install Lean 4 and Lake**:
   Follow the [Lean 4 installation guide](https://lean-lang.org/install/).

2. **Clone the Repository**:
   ```bash
   git clone https://github.com/npflueger/demazure.git
   cd demazure
   ```

3. **Build the Project**:
   Use the Lake build tool to compile and set up dependencies.
   ```bash
   lake exe cache get
   lake build
   ```

For further information about working with Lean 4/Mathlib projects, consult the [Mathlib project guide](https://leanprover-community.github.io/install/project.html).

## Generative AI disclosure

Portions of this repository were built with the assistance of generative AI, primarily OpenAI Codex and Claude Code. The extent of such tool use varies in different parts of the project. The file ``AGENTS.md`` contains instructions given to these agents when writing proofs, and may be informative about the manner in which these tools have been used. In particular, proofs that have been written primarily by an AI tool are indicated with a comment identifying the model used. The overall design, and all formalized theorem statements, were written by the author.
