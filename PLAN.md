# PLAN — Learn Lean from Scratch, by Building Verified Logic Tools

A multi-course, learn-by-doing curriculum. You are a **pro coder** with **no Lean experience** and
**no formal-logic training** — so every concept is taught as a runnable build, the **logic is taught
gently and just-in-time** (only when the formalization needs it, always in service of the proof), and
**every result is machine-checked**. The dream — **two provers you coded and proved correct** (natural
deduction and resolution), a SAT solver with a verified certificate checker, Euclid made rigorous, and
the logical heart of Gödel's incompleteness — is the destination; we get there one proof at a time.

The structure is a **tower of vertical slices**: each *course* is a complete, working capability, ending
in something you can *run* or a theorem the kernel *certifies*. We build **`Principia`** (a nod to
*Principia Mathematica* — the system Gödel's theorems were about; rename freely), a real Lean library,
growing it module by module until it contains **two verified provers** (natural-deduction and
resolution), a SAT solver with a verified UNSAT-certificate checker, machine-checked Euclidean
propositions, and a machine-checked incompleteness theorem.

This mirrors how you learned in `../Physics` (build `worldline`), `../LLM` (build a DL framework), and
`../Compiler` (build a Swift compiler): one real artifact, one concept per directory, a progressive
ladder of implementations, validated against a read-only oracle, taught by an `explainer.qmd`. The
twist: in Lean **the oracle is the kernel itself** — a `sorry`-free `lake build` *is* the green test.

---

## 0. Principles

1. **Real artifacts, not toys.** One real library (`Principia`) — two provers, a solver + checker,
   Euclid, Gödel — that actually builds, runs, and is machine-checked end to end.
2. **Always a working capability.** Each course is a vertical slice that builds green and shows
   something — a prover you `#eval`, a solver you run on DIMACS, a theorem the kernel certifies. We
   never have half a theory; we have a complete, checked piece.
3. **Learn by doing, one concept per directory.** Each concept = an explainer + a skeleton you fill in
   (`sorry`) + a verified solution + checks.
4. **Logic & proof taught gently, just-in-time, in service of the formalization.** When a concept needs
   a quantifier, an inductive predicate, a model, a fixed point, build the *idea* from zero — concept
   first, symbols second — and only because the next formalization asks for it. Never logic-for-its-own-
   sake. **And be generous:** assume no prior logic, motivate every definition, walk each proof, tactic,
   and error message line by line. Err toward over-explaining the new idea — a terse explainer is a bug.
5. **Honesty is the spine.** Where `../Physics` chased accuracy and conservation, here we chase
   *trust*: no stray `sorry`, no cheating `axiom`. Every keystone is audited with `#print axioms` and
   must rest only on Lean's accepted axioms (`propext`, `Classical.choice`, `Quot.sound`) — never
   `sorryAx`. A proof that "passes" by assuming what it should prove is wrong, and the auditor catches it.
6. **Everything is checked automatically** via the three tiers (§3).
7. **Oracle-based validation.** The Lean kernel, Mathlib, and battle-tested external tools
   (CaDiCaL, Z3/CVC5) are read-only answer keys — never code we fudge to pass.

---

## 1. The oracles (READ-ONLY answer keys)

| Oracle | What it is | How we use it |
|---|---|---|
| **The Lean kernel** | the type-checker | The primary oracle. A `sorry`-free `lake build` is a machine-checked proof. There is no fudging it. |
| **`#print axioms`** | the axiom auditor (`tooling/`) | Every keystone must depend only on `propext`/`Classical.choice`/`Quot.sound`. A `sorryAx` dependency = fail. |
| **Mathlib** | the standard math library | The answer key for mathematical facts (used heavily in Euclid; available throughout). |
| **CaDiCaL / DIMACS / LRAT** | a real SAT solver + standard formats | Differential-test our solver; feed real UNSAT certificates to our verified checker. |
| **Z3 / CVC5** | SMT solvers | Discharge the diagrammatic side-conditions in the Euclid (LeanEuclid) framework. |
| **Reference formalizations** | FFL-Foundation, LeanEuclid, Lean-core LRAT checker | Read-only designs we check our approach against (never copy blindly). |

All read-only. They are the spec and the answer key, never code we change to win.

---

## 2. Repository layout

```
/Users/elucterio/Lean/
├── PLAN.md                 # this file — the curriculum
├── CLAUDE.md               # conventions (read every session)
├── references/             # VENDORED, READ-ONLY (the books you asked to download):
│   ├── NNG4/               #   leanprover-community/NNG4            (Apache-2.0)
│   ├── logic_and_proof/    #   leanprover-community/logic_and_proof (Apache-2.0)
│   ├── theorem_proving_in_lean4/   # leanprover/theorem_proving_in_lean4
│   └── mathematics_in_lean/        # leanprover-community/mathematics_in_lean (Apache-2.0 / CC-BY-4.0)
└── course/
    ├── GUIDE.md            # the learner's manual (start here to learn)
    ├── README.md           # one-paragraph orientation + commands
    ├── Makefile            # task runner (setup / build / test / lab / explainer / axioms / docs)
    ├── _quarto.yml         # Quarto config (HTML + Typst/PDF explainers)
    ├── lean-toolchain      # pinned: leanprover/lean4:v4.31.0 (current stable)
    ├── lakefile.toml       # the Principia library — pure Lean 4, NO Mathlib (deps enter via sub-projects)
    ├── Principia/          # THE ARTIFACT — one Lean library, the modules below
    │   ├── Logic/          #   syntax · semantics (propositional + FOL)     (the shared spine)
    │   ├── NatDed/         #   natural-deduction system + prover            (Course 1)
    │   ├── Resolution/     #   CNF · resolution system + prover             (Course 2)
    │   ├── Sat/            #   CNF · DPLL/CDCL · verified LRAT checker       (Course 3)
    │   ├── Euclid/         #   (LeanEuclid sub-project, own toolchain pin)   (Course 4)
    │   └── Goedel/         #   diagonal lemma · abstract incompleteness      (Course 5)
    ├── tooling/            # oracle harness: axiom auditor, DIMACS/LRAT runners, differential tests
    ├── _TEMPLATE-concept/  # copy this to author a new concept
    ├── 00-foundations/     # Course 0: the language & tactics (NNG · TPIL · Logic&Proof · MIL)
    ├── 01-natural-deduction/
    ├── 02-resolution/
    ├── 03-sat/
    ├── 04-euclid/
    └── 05-goedel/
```

The `Logic/` core (syntax + semantics, propositional and first-order) built in Course 1 is the **shared
spine** reused by `NatDed/`, `Resolution/`, `Sat/`, and `Goedel/`; `Euclid/` sits on Mathlib +
LeanEuclid instead. So `Principia` is genuinely one accumulating library, not a pile of toys. Verified
code from a concept **graduates** into `Principia/` so later concepts import it.

---

## 3. The three testing tiers (how an exercise is checked)

1. **Tier 1 — Formal proof (the main mode).** skeleton = a theorem stated with `sorry` + tips;
   solution = the discharged proof. `make lab C=<dir>` builds the skeleton (red until you fill it in);
   `make test` builds the solutions (always green). The kernel is the grader.
2. **Tier 2 — Computational.** Our provers and solver are real programs. `#eval` / `#guard` /
   `decide` / `native_decide` run them on concrete inputs and check the answers (e.g. "the prover
   finds a derivation of Peirce's law", "resolution refutes ¬φ", "the solver's model satisfies this
   CNF"). No proof needed — the computation is the check.
3. **Tier 3 — Reference / differential.** Mathlib as the math answer-key; **CaDiCaL** as a
   differential oracle for the SAT solver (same SAT/UNSAT verdict on DIMACS instances); **Z3/CVC5**
   for Euclid's diagrammatic side-conditions; reference formalizations as designs we check against.

The honesty rule (`#print axioms`, no stray `sorry`/`axiom`) runs over every keystone — it is the
Lean analog of "never fudge the oracle."

---

## 4. Concept-directory convention

Every concept lives in `course/<NN-course>/NN-concept/`:

```
NN-concept/
├── README.md       # objective, prereqs, the rung ladder, "definition of done"
├── explainer.qmd   # THE LESSON — the logic/math it needs, taught gently from zero, then the Lean
├── Skeleton.lean   # the BARE statements YOU prove (`set_option warningAsError true` + theorem … := by sorry) — no inline tips; hints live in the explainer
├── Solution.lean   # verified answer key + a `## Checks` block (#eval/#guard + #print axioms); built by `make test`
└── figs/           # (optional) diagrams for the explainer (e.g. ND derivation trees, Euclid figures)
```

**The skeleton↔solution toggle.** `make test`/`lake build` builds `Solution.lean` → always green → the
repo always builds. `make lab C=<dir>` builds `Skeleton.lean` → red (`sorry`) until you discharge it →
green. Copy `_TEMPLATE-concept/` to author a new one.

**Lessons render in place.** `make explainer C=<dir>` / `make docs` render each `explainer.qmd` to
`explainer.html` **and** `explainer.pdf` (Typst, no LaTeX) *beside the source in the concept directory*
— not into a separate build dir — so the lesson sits next to the code it teaches.

Some concepts have a multi-rung ladder (e.g. the SAT solver: DPLL → unit-prop soundness → CDCL → LRAT
checker); others are a single rung. Each rung is independently buildable and checked.

---

## 5. The courses (curriculum)

### Course 0 — Foundations: the language & tactics  *(fuller, since new to both)*

The on-ramp. Learn Lean *and* the idea of a formal proof, by doing, drawing on the four vendored books.
We **mirror** key exercises locally as skeleton→solution so they're checked in *our* repo.

- **M0 — setup** — `elan`/`lake`/VS Code, `lake exe cache get` (prebuilt Mathlib), the loop, first proof.
- **0.1 Natural Number Game** — `rfl`, `rw`, `induction`, `simp`; build ℕ from Peano. *(NNG4)*
- **0.2 Propositions as types & tactics** — `→ ∀ ∃ ∧ ∨ ¬`, tactic mode; what a proof *is*. *(TPIL 3–6)*
- **0.3 Inductive types & recursion** — define your own types; structural & well-founded recursion.
  *(TPIL 7–8 — the technical core for everything after.)*
- **0.4 Logic, gently** — natural deduction on paper ↔ Lean; classical vs. constructive; the semantics
  of propositional logic, from zero. *(Logic and Proof — sets up Courses 1–2 directly.)*
- **0.5 Mathlib fluency** — `simp`/`linarith`/`ring`/`decide`, `exact?`/`apply?`, structures & type
  classes; enough to be productive. *(MIL, selected.)*

### Course 1 — A verified theorem prover for natural deduction  *(prover #1 — you code it)*

Build the **first of two provers**. Define the logic, prove the metatheory, then *code a proof search*
that finds natural-deduction derivations — and trust it because you proved it sound (and, propositionally,
complete).

| Slice | Payoff | Keystone |
|---|---|---|
| 1.1 Syntax `Form` (inductive) + notation | pretty-printed formulas, `#eval` | |
| 1.2 Semantics: valuations, `eval`, `⊨`, tautology | a truth-table checker you run | |
| 1.3 Natural deduction `Γ ⊢ φ` (inductive rules) | a checked ND proof of Peirce's law | |
| 1.4 **Soundness** `Γ ⊢ φ → Γ ⊨ φ` | — | ✅ induction on derivations |
| 1.5 The **prover** (proof search), FOL-ready data | `#eval prove φ` returns a derivation | |
| 1.6 **Completeness (propositional)** `Γ ⊨ φ → Γ ⊢ φ` | `⊢ φ ↔ ⊨ φ`; verified decision procedure | ✅ (hard) Lindenbaum / max-consistent sets |
| 1.7 *(stretch)* lift to first-order: terms, quantifiers, substitution | prover runs on FOL (semi-decidable) | soundness extends; **FOL completeness = stretch (Henkin)** |

*Reference:* FFL-Foundation (`Classical.soundness`/`.completeness`, full FOL completeness via Henkin);
Logic and Proof. **Milestone M1.**

### Course 2 — A verified resolution prover  *(prover #2 — the automated-reasoning bridge)*

The **second prover**, and the bridge to SAT. Resolution is refutation-based: to prove `φ`, convert
`¬φ` to CNF and derive the empty clause `□`. One rule, machine-oriented — the ancestor of every modern
SAT/SMT engine. Reuses Course 1's syntax & semantics.

| Slice | Payoff | Keystone |
|---|---|---|
| 2.1 CNF conversion `Form → Clauses` (NNF + Tseitin) | `#eval` a formula's clause set | preserves (un)satisfiability |
| 2.2 The resolution rule + derivations (inductive); the empty clause `□` | a refutation built by hand | |
| 2.3 The **resolution prover** (saturation / given-clause search) | `#eval prove φ` — a decision procedure (propositional) | |
| 2.4 **Soundness** `□ ∈ Res*(S) → S unsatisfiable` | — | ✅ resolution preserves satisfiability |
| 2.5 **Refutation-completeness (propositional)** `S unsat → □ ∈ Res*(S)` | with 2.1 ⇒ verified decision procedure; tie to Course 1: `⊢_ND φ ↔ resolution refutes ¬φ` | ✅ semantic tree / induction on variables |
| 2.6 *(stretch)* first-order resolution: terms, **unification (mgu)**, the lifting lemma | the prover runs on FOL (refutation-complete, semi-decidable) | soundness extends; **refutation-completeness via Herbrand + lifting = stretch** |

*Reference:* classic resolution metatheory; unification implementations in Lean; the SAT connection
below. **Milestone M2.**

### Course 3 — A verified SAT solver  *(resolution, made practical)*

CDCL *is* resolution under the hood — learned clauses are resolvents, and DRAT/LRAT UNSAT certificates
are resolution (RUP) proofs. So Course 2 is exactly the theory this course makes fast and trustworthy.
Reuses the `Logic/`/`Resolution/` CNF machinery.

- 3.1 CNF / literals / clauses / models — reuse the `Resolution/` representation.
- 3.2 **DPLL** — unit propagation, pure-literal, splitting; a real Lean program; `#eval solve`.
- 3.3 **Model soundness** (✅): a returned model really satisfies the CNF (by evaluation).
- 3.4 **Unit-propagation soundness** (✅ keystone): propagation preserves satisfiability.
- 3.5 **Toward CDCL** — clause learning (= resolution!), conflict analysis, backjumping, watched
  literals; differential-tested against **CaDiCaL** on DIMACS. *(Full CDCL verification = out of scope.)*
- 3.6 **The verified LRAT certificate checker** (✅ keystone): `check proof cnf → cnf.Unsat`. The
  honest, real-world target — an untrusted fast solver emits an LRAT (resolution) proof → our verified
  checker validates it → UNSAT is trusted.

*Reference:* Lean core's `Std.Tactic.BVDecide.LRAT.check_sound`; cake_lpr; SATurn. **Milestone M3.**

### Course 4 — Euclid's *Elements* in Lean  *(LeanEuclid + SMT)*

- 4.1 **Why Euclid isn't rigorous as written** — the I.1 "two circles meet" continuity gap; the I.4
  superposition gap. The honesty theme, made geometric.
- 4.2 Set up **LeanEuclid** (system "E" + diagrammatic side-conditions offloaded to Z3/CVC5 via
  `euclid_apply`/`euclid_finish`). Runs as a sub-project on its own pinned toolchain (v4.19).
- 4.3 **Prop I.1** — equilateral triangle (the canonical first; the hidden continuity axiom made honest).
- 4.4 **I.4 (SAS), I.5 (pons asinorum)** — a short chain.
- 4.5 *(stretch)* **I.47 — Pythagoras**, or its analytic Mathlib counterpart as a synthetic-vs-analytic
  contrast.

*Reference:* LeanEuclid (Murphy et al., ICML 2024); system E (Avigad–Dean–Mumma); Mathlib Euclidean
geometry. **Milestone M4.**

### Course 5 — Gödel's incompleteness  *(the capstone — study + a real proof)*

Prove the logical heart; *read* the heavy arithmetization from a library that's done it, then attempt
our own as the marked stretch. Sequenced so each rung stands alone.

- 5.1 **The landscape** (explainer) — what the theorems say; Gödel numbering, diagonal lemma,
  provability predicate, D1–D3, Rosser, the second theorem, Löb.
- 5.2 **Tarski's undefinability of truth** (✅) — a short diagonal argument; warm-up.
- 5.3 **The diagonal / fixed-point lemma** (✅ keystone), abstractly.
- 5.4 **Abstract first incompleteness** (✅ keystone) — assume representability + derivability
  conditions as a black-box interface (Popescu–Traytel pattern); derive incompleteness.
- 5.5 **Lawvere's fixed-point theorem** (✅ keystone, *novel*) — the one categorical diagonal yielding
  Cantor, Russell, Tarski, *and* Gödel as instances. No public Lean→Gödel formalization found, so this
  is a small genuine contribution and an elegant finale.
- 5.6 **Lean on Foundation** (✅) — `import` FFL-Foundation and instantiate our abstract theorem against
  its full arithmetized provability predicate, for the real concrete result.
- 5.7 *(stretch)* **Attempt our own arithmetization** — Gödel-numbering + a Σ₁ provability predicate +
  representability, leaning on Foundation wherever it gets too heavy. The clearly-marked hard goal.

*Reference:* FFL-Foundation (first & second incompleteness, Rosser, Löb, in Lean 4); O'Connor (Coq);
Paulson (Isabelle/HF); Popescu–Traytel (the abstract pattern); Yanofsky/Lawvere. **Milestone M5.**

---

## 6. Milestones

- **M0** — setup green; the learn-by-doing loop works; first proof. *(Course 0)*
- **M1** — machine-checked **soundness** of natural deduction + a running prover. *(Course 1)*
- **M2** — a **refutation-complete resolution prover** + a verified propositional decision procedure.
  *(Course 2)*
- **M3** — a **verified UNSAT certificate checker** with a working solver front-end. *(Course 3)*
- **M4** — machine-checked **Euclid I.1** (and the early chain). *(Course 4)*
- **M5** — a machine-checked **abstract incompleteness theorem** (+ Lawvere; + Foundation). *(Course 5)*

---

## 7. Honest difficulty flags

- **ND FOL completeness** (1.7): hard (Henkin) — a clearly-marked stretch, not a core deliverable.
- **Resolution FOL refutation-completeness** (2.6): hard (Herbrand + lifting lemma) — a stretch; the
  FOL *prover itself* (with unification) is in scope, the completeness proof for it is the reach.
- **Full CDCL verification**: infeasible at course scope — the **LRAT checker** is the right target.
- **Euclid I.47**: a stretch; I.1/I.4/I.5 are solidly tractable.
- **Our own Gödel arithmetization** (5.7): very hard — we prove the **abstract** theorem (5.2–5.6) and
  lean on Foundation for the concrete; 5.7 is the optional reach.

---

## 8. How we work (pointer)

Day-to-day conventions — the skeleton↔solution mechanism, the no-`sorry`/axiom-audit oracle policy,
authoring a concept, the toolchain pins, the commands — live in `CLAUDE.md`. The learner's manual is
`course/GUIDE.md`. Course 0 and Courses 1–2 are concrete; later courses are an honest outline, refined
as we reach them — always keeping a buildable, checked capability at every step.
