# Naming and encoding decisions

This file records the naming and encoding decisions of the Lean 4 / mathlib formalization of

> G. Ullman, *Symmetry Between Perspectives: Invariant Calibration and Symmetry Lifts*,
> Zenodo version 14, DOI
> [`10.5281/zenodo.23040249`](https://doi.org/10.5281/zenodo.23040249).

Labels such as `def:data` and `thm:strict` are LaTeX labels of that article. Which
declaration formalizes which result, and under which hypotheses, is recorded in
[`LEAN_COVERAGE.md`](LEAN_COVERAGE.md); the recorded build and axiom audit are in
[`BUILD_LOG.txt`](BUILD_LOG.txt).

## 1. Foundations

1. **Categories, not groupoids.** The ambient hypothesis is `[Category O]`. No general declaration
   assumes that `O` or `S` is a groupoid. `OEData.base_hom_isIso` (`rem:groupoid`) takes the
   groupoid property of `O` as the explicit hypothesis `hO : ∀ {x y : O} (f : x ⟶ y), IsIso f`; its
   converse `OEData.hom_isIso_of_base_isIso` assumes that every arrow of `S` is invertible. Neither
   is packaged as a `Groupoid` instance.
2. **Two-layer structure.** `OEData G p` extends `NormalizedPreDatum G p`, which carries clauses
   (N1)–(N5) of `def:data` without the invertibility part of (N5), by the single field
   `p_faithful` ((N6)). The generated projections are `NormalizedPreDatum.act`, …; dot notation
   (`d.act`, `d.chi_comp`, …) and `where`-constructors work as usual, and `OEData.mk` takes the
   pre-datum and `p_faithful`.
3. **Invertibility of the vertical arrows is derived, not assumed.** `OEData.ltrans_isIso` (an
   instance) follows from `p_ltrans` and full faithfulness (`isFull` + `p_faithful`). `Λ`,
   `Λ_comp_p`, `idIsoΛ` and `ΛIsoId` use `inv (d.ltrans g x)`; `OEData.ltransIso` (with
   `ltransIso_hom`, `ltransIso_inv`) and `OEData.p_map_inv_ltrans` package it. So
   `NormalizedPreDatum` alone is strictly weaker than the article's (N1)–(N5), and
   `Examples/NonFaithful` depends on exactly that: `nonfaithfulPreDatum` is a pre-datum, and
   invertibility of ℓ is a separate instance.
4. **A redundant field.** `NormalizedPreDatum.act_free` is not a clause of `def:data`. It follows from
   `act_mul`, `base_coord` and `coord_base` (`lem:coordinates`), which is proved in
   `OEData.coordinate_identities` (MinSpecCorrespondence). It adds no hypothesis beyond `def:data`,
   and several Core proofs use it directly.
5. **Weak and strict normal form.** `productNormalForm d : O ≌ S × Pair G` and
   `projectionEquivalence` are the weak (equivalence) form of `thm:normalform`. The article's strict
   isomorphism of categories is the pair `normalFormTo_comp_normalFormFrom` /
   `normalFormFrom_comp_normalFormTo` in `NormalForm`.
6. **Multiplication order.** In `StrictAut`, `AutBoxG`, `AutBoxGOver`, `AutBoxGθOver`,
   `AutEquivOver` and `HolLift`, `(e * e').hom = e'.hom ⋙ e.hom`. So `e₂ = Λ_g · e₁` in
   `existsUnique_ΛHom_mul_of_Φ_eq` is `rigidity`'s `F₂ = F₁ ⋙ Λ d g`, and the article's
   `Ã Λ_δ Ã⁻¹` has underlying functor `liftFunctor A.inv ⋙ ΛFun δ ⋙ liftFunctor A.hom`. In
   `SingleObj`, composition is `f ≫ g = g * f` (multiplication in operator order), as in the
   article.
7. **Imports.** Every module imports the specific mathlib files it uses; no module imports all of
   `Mathlib`. The audit's declaration count depends on this import surface, because it includes
   generated auxiliary constants (see `BUILD_LOG.txt`).

## 2. Names and namespaces

8. **`OEData.IsInvariant d F`** (strict invariance `R_h ⋙ F = F`, `prop:residual`) is namespaced,
   because mathlib already has a root `IsInvariant` (`Mathlib/Dynamics/Flow.lean`). Use it as
   `d.IsInvariant F`; a bare `IsInvariant d F` resolves to mathlib's definition.
   `IsInvariantNatTrans` is at the root.
9. **`OEData.actFunctor_covers_id`** (Residual) has the same statement, `d.actFunctor h ⋙ p = p`, as
   `LocalLifts.actFunctor_comp_p` (the sibling in the minimal specification is
   `MinSpec.actFunctor_comp_p`). It has its own name because Residual does not import LocalLifts,
   and the entry file imports both, so one name in both modules would clash. Its docstring records
   the duplication.
10. **`IsVertical p v`** (`∃ h : p.obj x = p.obj y, p.map v = eqToHom h`) and its closure lemmas
    `IsVertical.id` / `eqToHom` / `comp` / `inv` live in `NormalForm`. The definition follows the
    unlabeled paragraph right after `def:data`; it is neither `def:vertical-trivial` nor (N5),
    although both use it.
11. **The residual action** is the root `residualAction d F hF s : G →* Aut (F.obj (d.base s))`,
    built from the vertical arrows `OEData.vertArr` and `OEData.IsInvariant.residualHom`; Calibration
    and RecordsCalibration use it.
12. **Local duplicates.** `baseChange_twistFactor_mul` (BaseChange) states the coboundary identity
    whose canonical form is `OECocycle.coboundary_mul`; `baseChange_twistFactor_eq_coboundary`
    (BaseChangeCocycle) identifies the two by `rfl`.
13. **Lift groups and aliases.** The article's lift groups `Sym_H(p)` and their twisted versions
    are `AutBoxG`, `AutBoxGOver`, `AutBoxGθ` and `AutBoxGθOver`; comments in Core abbreviate them
    as `Aut□_G`. `strict_lift`, `exact_sequence` and `strict_liftθ` are aliases of `lift_exists`,
    `unbundled_lift_classification` and `twisted_lift_exists`.
14. **Existential statement and witness.** `unrestricted_calibration_exists` is stated
    existentially; its witness is `unrestrictedCalibration`.
15. **Helper namespaces.** Local helper lemmas live in namespaces to avoid clashes: `ProductModel`
    (`productHom_ext`, `eqToHom_fst`, a global `@[simp]` lemma once imported), `LocalLifts`,
    `Components`, `AutEquivOver`, `ComponentsSwapExample`, `InvFun`, `ResidualCategory`,
    `Calibration`, `OECocycle`, `TwistExample`, `RecordsExample`, `RecordsCalibration`,
    `TwoObjectExample`, `NonFaithful`. The C₂ helpers (`c2Hom`, `c2MulEquiv`, `c2Gen`, …) exist
    twice, in `TwistExample` and `RecordsExample`, because Records does not import Twist. Holonomy
    has no namespace: its declarations are root-level, grouped in sections.
16. **The four modules of `sec:lean-modules`.** All declarations of `Comparisons` and `Implementations`
    live in namespace `ResidualData`, so they are reached by dot notation on `ResidualData S C G`
    of `Residual`. `Examples/ComplexObstruction` uses namespace `ComplexObstruction`, and
    `Examples/RecordsRecovery` uses namespace `RecordsRecovery`.
17. **Explicit data binders.** Some declarations take `(m : MinSpec G p)` or `(d : OEData G p)` as
    an explicit binder because their statement does not mention it (`MinSpec.hom_ext`,
    `MinSpec.no_strict_retraction`, `MinSpec.descent`, `OEData.descent`, `OEData.natTrans_descent`,
    …). Dot notation (`m.descent F`) works.

## 3. Representation choices

18. **Structures rather than subtypes.** `InvFun d C` and `InvFun.Hom` are structures (fields
    `functor`/`invariant` and `nat`/`invariant`). A subtype wrapped in a `def` gives terms that are
    ill-typed at instance transparency, which breaks `rw`/`simp`. Objects are exactly the invariant
    functors and arrows exactly the invariant natural transformations.
19. **Labeled and unlabeled record spaces (`sec:records`).** Both encodings are present, and they
    carry different weight.
    - *Unlabeled.* `L₀ τ : RecDom ⥤ ModuleCat.{0} ℝ` is the article's `L`. Here `LA ≠ L` is the
      informative statement: `recA_comp_L₀_ne (τ) (hτ : τ ≠ 0) : recA.hom ⋙ L₀ τ ≠ L₀ τ`. The
      proof evaluates on the index record `recIdxRecord` and uses that the `eqToHom` casts are
      morphisms of `ModuleCat ℝ`, hence linear (`L₀_eqToHom_hom_apply_of_eq`); no equality of
      carrier types is needed. Corollaries: `recA_not_mem_strictLawStabilizer_L₀`,
      `recH_not_le_strictLawStabilizer_L₀`.
    - *Labeled.* `Lℓ τ = recLabel.prod' (L₀ τ) : RecDom ⥤ Pair RecDom × ModuleCat.{0} ℝ` is the
      literal reading of "explicitly labeled vector spaces": the label of `L(I)` is its observation
      domain. The label factor `Pair RecDom` has exactly one arrow between any two objects, so it
      adds no morphism data, and forgetting labels gives back the unlabeled law
      (`Lℓ_comp_snd : Lℓ τ ⋙ Prod.snd = L₀ τ`, by `rfl`). At this level the inequality follows
      from the labels alone, and the triviality of the strict stabilizer from the labels together
      with the thinness of the base (`strictLawStabilizer_Lℓ_eq_bot`, proved for `Lℓ τ`).
20. **The parameter `τ`.** The membership characterization `mem_recordSpace_full_iff` needs `0 < τ`.
    The law inequality needs only `τ ≠ 0`, and is stated that way. The case `τ = 0` is not stated:
    it would require deciding an equality of carrier types, which Lean cannot do here.
21. **Signs as `G = ℤˣ`**, acting on real vector spaces by `((ε : ℤ) : ℝ) • ·`, with
    `recData = productData RecDom ℤˣ`. The sign group is represented exactly, not as an abstract
    `C₂`, so that the action on records is definitional.
22. **`Pair PUnit` as the terminal base** in `ex:invariant`, where the article writes `*`. That it is
    terminal is proved, not assumed: `pairPUnit_obj_eq` (any two objects are equal) and
    `pairPUnit_functor_eq` (any two functors into it are equal).
23. **`Fin 2` with its preorder category structure** as the two-object base of the example after
    `prop:nocleavage`: one nonidentity arrow (`arrow01`), hom-sets subsingleton
    (`hom_subsingleton`), no arrow backwards (`hom_one_zero_isEmpty`), and `arrow01_not_isIso`.
    Consequently `StrictAut (Fin 2)` is trivial (`strictAut_eq_one`) and `H = ⊤ = ⊥` (`top_eq_bot`)
    is the only possible base subgroup, so the example isolates the vertical phenomenon.
24. **Universes.** The `Groupoid` instance on `Pair X` has `Hom _ _ := PUnit` with a *free* universe.
    The hom universe of `HolTotal Γ G = SingleObj Γ × Pair G` is therefore an extra free parameter,
    and a bare reference to a lemma about it can leave universe metavariables. Three proofs work
    around this without changing any statement: the holonomy bundle inlines two proofs,
    `holonomy_not_OEData` repeats the argument of `holonomy_not_normalized` instead of invoking it,
    and `swapAut_obj` is proved by `⟨rfl, rfl⟩` rather than by pairing its two component lemmas.
    `Examples/NonFaithful` fixes `PUnit.{1}` (`Discrete PUnit.{1}`, and
    `nonfaithfulPreDatum K : NormalizedPreDatum PUnit.{1} _`) while `K` stays universe-polymorphic;
    this rules out a presentation group `PUnit.{u+1}` living in `K`'s universe.
25. **The general statements of `sec:lean-modules`** (`Comparisons`, `Implementations`) are stated in the
    strict product normal form (base `S × Pair G`, datum `productData S G`) for an arbitrary base
    category `S` and an arbitrary target `C`. They are not separately restated for an arbitrary
    normalized datum; the normal-form and residual-data theorems provide the passage.
26. **Realification** in `Examples/ComplexObstruction` is restriction of scalars,
    `realification := ModuleCat.restrictScalars (algebraMap ℝ ℂ)`, so the target categories are
    `ModuleCat ℂ` and `ModuleCat ℝ`.
27. **Measurement calculations** (`Examples/RecordsRecovery`). A procedure is `Procedure τ` with the
    two separate conditions `IsEven` and `RespectsRestrictions`. The sign-orbit target is
    `Set`-valued: `orbitFunctor τ : RecDom ⥤ Type`. The reference-observation recovery
    (`reference_determines_sign`, `reference_recovers_value`) is stated as scalar identities in
    `ℝ`, not at the level of the record functors.
