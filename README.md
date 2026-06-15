# demazure

This repository contains formalizations about the basic theory of the *Demazure product* on almost-sign-preserving permutations, as developed in the following paper.

N. Pflueger, [An extended Demazure product on integer permutations via min-plus matrix multiplication](https://arxiv.org/abs/2206.14227)

The code includes full formalizations of the main theorems of that paper, following the style, definitions, and proof structure closely. The repository also includes some additional results not included in the paper, especially the classification of Demazure factorizations of 321-avoiding permutations (not necessarily of finite length).

## Project Structure

The Lean development in `Demazure/` is organized as follows. Read the diagram
top to bottom: arrows point from prerequisites to files that import them.

```text
+-----------------------------+          +-----------------------------+
| Utils.lean                  |          | Valley.lean                 |
| Generic helper lemmas       |          | Tools for tracking minima   |
|                             |          | and argmins.                |
+--------------+--------------+          +--------------+--------------+
               |                                        |
               |                                        v
               |                         +--------------+--------------+
               |                         | SlipFace.lean               |
               |                         | Slipfaces and operations    |
               |                         | on them.                    |
               |                         +--------------+--------------+
               |                                        |
               +------------------------+---------------+
                                        |
                                        v
                         +--------------+--------------+
                         | AspPerm.lean                |
                         | ASP permutations, inversion |
                         | sets,weak                   |
                         | orders, ⋆ and ◃ predicates  |
                         +--------------+--------------+
                                        |
                         +--------------+--------------+
                         |                             |
                         v                             v
        +-----------------------------+     +-----------------------------+
        | InvSet.lean                 |     | Submodular.lean             |
        | Abstract ASP inversion sets |     | Submodular slipfaces;       |
        | and reconstruction          |     | ⋆ and ◃ on ASP.             |
        +--------------+--------------+     +--------------+--------------+
                         |                             |
                         +--------------+--------------+--------+
                                        |                       |
                                        v                       v
                         +-----------------------------+   +-----------------------------+
                         | Avoiding321.lean            |   | ReducedProducts.lean        |
                         | 321-avoiding permutations   |   | Reduced products            |
                         | and behavior of ⋆ on them   |   | and relations to ⋆ and ◃    |
                         +--------------+--------------+   +--------------+--------------+
                                        |                                  |
                                        v                                  v
                         +-----------------------------+   +-----------------------------+
                         | Tableaux.lean               |   | Reduction.lean              |
                         | Hecke                       |   | Greedy and stingy           |
                         | factorizations and          |   | characterizations;          |
                         | set-valued tableaux         |   | reduction theorems          |
                         +-----------------------------+   +--------------+--------------+
                                                                           |
                                                                           v
                                                                  +--------+----------------+
                                                                  | Transpositions.lean     |
                                                                  | Adjacent transposition  |
                                                                  | formulas for product    |
                                                                  | and contraction         |
                                                                  +-------------------------+
```

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

For futher information about working with Lean4/Mathlib projects, consult the [Mathlib project guide](https://leanprover-community.github.io/install/project.html).

## Generative AI disclosure

Portions of this repository were built with the assistance of generative AI, primarily OpenAI Codex and Claude Code. The extent of such tool use varies in different parts of the project. The file ``AGENTS.md`` contains instructions given to these agents when writing proofs, and may be informative about the manner in which these tools have been used. In particular, proofs that have been written primarily by an AI tool are indicated with a comment identifying the model used. The overall design, and all formalized theorem statements, were written by the author.