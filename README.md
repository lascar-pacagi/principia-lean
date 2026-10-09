# Principia — Learn Logic by Building Proofs in Lean

A practical Lean 4 course for programmers with no prior experience in formal logic or theorem proving.
Learn one concept at a time while building **Principia**, a library of logic tools and machine-checked
proofs. Lessons explain the ideas, exercises give you practice, and Lean checks your answers.

## The course

| Part | What you build and learn |
|---|---|
| 0. Foundations | Types, propositions, proof tactics, recursion, and induction |
| 1. Natural deduction | A proof system and a verified theorem prover |
| 2. Resolution | Conjunctive normal form, resolution, and a second verified prover |
| 3. SAT | SAT solving and a verified checker for unsatisfiability certificates |
| 4. Euclid | Formal proofs of geometric propositions |
| 5. Gödel | Diagonal arguments, Tarski's theorem, and abstract incompleteness |

Start with the [learner's guide](course/GUIDE.md) and the
[first lesson](course/00-foundations/00-setup/explainer.qmd).
The [curriculum](PLAN.md) gives the full roadmap.

## Install and start

1. Follow the [official Lean installation guide](https://lean-lang.org/install/): install VS Code,
   the Lean 4 extension, and complete its setup. The extension provides the interactive proof view.
2. Have Git, Make, Bash, Perl, and Python 3.9 or later available. The commands below use a Unix shell,
   such as macOS, Linux, or WSL on Windows.
3. Clone the repository and build it:

   ```bash
   git clone https://github.com/lascar-pacagi/principia-lean.git
   cd principia-lean/course
   make setup
   make test
   ```

The project pins its Lean version in `course/lean-toolchain`; elan selects and downloads it as needed.
The core project has no Mathlib dependency.

Open the `course/` folder in VS Code, read the first lesson, and open
`00-foundations/00-setup/Skeleton.lean` to work on its exercises.

## The exercise loop

Each lesson has an `explainer.qmd`, a `Skeleton.lean` for your proofs, and a verified `Solution.lean`
to consult after trying. Replace each `sorry` placeholder with a proof, then run from `course/`:

```bash
make lab C=00-foundations/00-setup
```

Required exercises show **FAIL in red** until they check, then **PASS in green**. Where a lesson has
an `optional/Skeleton.lean`, the same command checks it separately: unfinished optional proofs show
**PENDING in yellow** and don't prevent the required lab from passing. Its answer key is
`optional/Solution.lean`.

Some skeletons already contain completed work. To start the course with empty exercises, run from
`course/`:

```bash
make reset DRY_RUN=1                  # preview the changes
make reset                            # reset all required and optional exercises to sorry
make reset C=00-foundations/00-setup   # or reset just one lesson, including its optional exercises
```

Resetting saves previous answers under `course/.exercise-backups/` and preserves exercise statements,
supplied code, and solution files. Copy a saved `Skeleton.lean` back to its original location to
restore those answers.

`make test` checks the supplied solution files. `make axioms` audits proofs for unfinished work and
unapproved axioms. Use `make lab` to check your own answers.

## Read lessons as HTML or PDF

Install [Quarto](https://quarto.org/docs/get-started/), then run from `course/`:

```bash
quarto render 00-foundations/00-setup/explainer.qmd --to all
```

Open the generated `explainer.html` or `explainer.pdf` beside the source. PDFs use Typst, so no LaTeX
installation is needed. Generated HTML and PDF files are not tracked in Git.

Run `make` from `course/` to see the available commands.
