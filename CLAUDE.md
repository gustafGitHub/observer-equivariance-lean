# CLAUDE.md — Lean formalization of "Observer Equivariance"

You are helping formalize a single mathematics paper in **Lean 4 + mathlib**. Read
this whole file before editing anything.

## What we are doing

The paper *Observer Equivariance as a Condition for Shared Physical Law* (G. Ullman)
proves a strict classification theorem for split principal `G`-fibrations in
groupoids: every base autoequivalence lifts to a `G`-equivariant cleavage-preserving
bundle autoequivalence, lifts are unique up to a normalized fiber translation, and
this assembles into a short exact sequence

```
1 → G → Aut□_G(O/p) → Aut(S) → 1.
```

The goal is to formalize that theorem and the two lemmas it rests on.

## Files

- `ObserverEquivariance.lean` — the v0 scaffold. Structure `OEData`, the functor `Λ`,
  the predicates, and the statements `strict_lift`, `rigidity`, `exact_sequence`.
  Every proof is currently `sorry`.
- `symmetry_observer_equivariance.tex` — the paper. **This is the ground truth for
  every theorem statement.** Section numbers in the Lean comments refer to it.

## Build & check

- Build with `lake build`. Build **often** — after every few edits, not at the end.
- Toolchain/mathlib are pinned in `lake-manifest.json` / `lean-toolchain`. The scaffold
  imports all of mathlib (`import Mathlib`); narrow it later if build time hurts.
- mathlib's Grothendieck-fibration / cartesian-morphism API may differ from what the
  scaffold assumes or from your priors — **verify names against the installed version**
  (grep `.lake/packages/mathlib`), do not trust memory.
- Track progress with the `sorry` count and with `#print axioms exact_sequence`. When a
  result is genuinely done its axiom list should contain no `sorryAx`.

## Hard rules (fidelity matters more than green builds)

1. **Do not change a theorem statement to make a proof go through.** The statements must
   match the paper. If a statement looks unprovable as written, STOP and explain why in
   chat — do not quietly edit it.
2. **Never make a `Prop` definition vacuous** (e.g. `:= True`) or weaken a hypothesis to
   force a proof. That produces a theorem that says nothing.
3. **Do not add axioms** to discharge a goal. If a proof seems to require a new field or
   assumption on `OEData`, propose it explicitly and say what it costs — adding structure
   changes what the theorem means.
4. `sorry` is fine as *intermediate* scaffolding. Leave a precise `-- BLOCKED:` note with
   the current goal state when you cannot close one, rather than hacking around it.
5. **Do not commit.** Edit files only; leave all `git` commits to the author.
6. The mathematics is the author's. Your job is faithful translation, not "improving" or
   re-deriving the argument. Surface mathematical doubts as questions.

## Known fidelity debt in v0 (these are gaps, not bugs to paper over)

The scaffold is deliberately weaker than the paper in three places. These must
eventually be repaid; flag if a proof silently relies on the weakening.

- `IsGEquivariant` is stated at **object level only**. The paper's `Aut□_G` also requires
  morphism-level equivariance **and cleavage preservation**. Strengthen it before claiming
  the theorem is faithful.
- `OEData` omits **splitness** of the cleavage (`chi_id`, `chi_comp`) and the cross-`g`
  coherence `actHom_mul`, left as TODO fields. They are needed for functoriality of `Λ`
  and for the lemmas.
- The cleavage is carried as hand-built data (`reind`, `chi`) rather than via mathlib's
  fibration API. Optional later refactor; keep statements stable across it.

## Attack order

0. **Make `OEData` elaborate.** Most friction is `eqToHom` direction in `p_actHom`,
   `p_chi`, `chi_act`, plus universe/binder details at the top of the file.
1. **Make `Λ` a real functor.** Prove the source identity in `Λ.map` (chosen-lift source =
   translated source, §4.2), then `map_id` / `map_comp`. This needs the splitness fields —
   add them (rule 3: propose, don't sneak).
2. **`rigidity` (§4.2)** — the mathematically substantive lemma. The pointwise element
   `g_s := k₂(s) k₁(s)⁻¹` is locally constant by cleavage preservation + `G`-stability,
   then constant because `S` is connected. Use mathlib's connectedness API
   (`CategoryTheory.IsConnected` / zigzag lemmas).
3. **`strict_lift` (§4.1)**, then finish **`exact_sequence` (§4.3)**: its surjectivity
   half is already wired to `strict_lift`; the kernel half is short given `rigidity`.
4. **Optional:** migrate to mathlib's fibration API and strengthen `IsGEquivariant` to the
   full `Aut□_G`. Only after this is the formalization fully faithful.

## eqToHom / object-equality discipline

This is the main grind (the paper reasons with on-the-nose object equalities). When
goals fill with `eqToHom` casts:

- Reach for `eqToHom_trans`, `eqToHom_refl`, `eqToHom_map`, `eqToHom_comp`,
  `comp_eqToHom`, `Functor.congr_hom`, `Functor.congr_obj` — **verify each name exists**
  in the installed mathlib before relying on it.
- `simp` with the `eqToHom` lemmas, `dsimp only`, and the category-theory dischargers
  (`aesop_cat`) clear most routine casts.
- Prefer rewriting object equalities with `subst` where a variable can be eliminated,
  before they propagate into morphisms.
- Keep `eqToHom` orientations consistent with the field definitions in `OEData`; flipping
  one usually means flipping its uses.

## Working protocol

Small steps; build after each; one lemma at a time, top of the attack order first. When
you finish a step, report the `sorry` count delta and any field you had to add. When
blocked, give me the goal state and your best guess at the missing lemma — don't spin.
