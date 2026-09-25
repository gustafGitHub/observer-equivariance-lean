# Changes — revision for *Symmetry Between Perspectives: Normal Forms, Descent, Calibration, and Lifts*

> **Current reference paper:** revision r6 of 25 September 2026, *Symmetry Between Perspectives:
> Invariant Calibration and Symmetry Lifts*; see "Article revision r6 and release build" at the end
> of this file. The title above and the r2 reference below describe this revision as first
> completed; the later sections record what changed since.

Reference paper: `perspectives_invariance_calibration_2026-09-05_r2.tex` (r2, 5 September 2026;
distributed with the article, not with this repository). All paper labels below (`def:data`,
`thm:strict`, …) refer to that file. The revision instruction (`Instruktion_till_Claude_Code.txt`,
"INSTR" below; an internal instruction file, not part of this repository) was written against an
earlier draft of the same article; r2 is a superset of it (it adds
`cor:invariant-calibration`, the information conditions in `sec:records`, and `sec:related`).

Baseline: commit `f3f9182` (single file `ObserverEquivariance.lean`, groupoid formulation, 18 audited
declarations). The archived `BUILD_LOG.txt` (20 August 2026) belongs to that snapshot. It does **not**
certify anything in this revision.

## Verification of this revision

> These figures are those of the September 2026 modular revision as first completed. They were
> superseded by the r4/r5 adoption at the end of this file: the current tree builds in 2272 jobs
> and audits 2766 declarations in 25 modules. The environment pins are unchanged throughout.

- Environment unchanged: `lean-toolchain` = `leanprover/lean4:v4.31.0-rc1`, mathlib rev
  `8834d3761934044a64c98afb757c1673fad03521`.
- `lake build` of the whole project succeeds (8518 jobs, no errors, no warnings).
- The root file ends with `#assert_standard_axioms_in_modules ObserverEquivariance`. It reports that
  all 2599 declarations in the 21 `ObserverEquivariance.*` modules depend only on `propext`,
  `Classical.choice` and `Quot.sound`. Any other axiom (including `sorryAx`) makes the build fail.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in Lean code. `scripts/audit.sh` strips
  comments before it scans, then runs the build and writes the raw log (default
  `BUILD_LOG_RAW.txt`).
- The unchanged pre-revision file (commit `f3f9182`) was rebuilt at the start of the revision in the
  same environment. It was green, with 18 audited declarations.

## Layout

- The development now lives in modules under `ObserverEquivariance/`. `ObserverEquivariance.lean`
  remains the entry point: it imports every module and runs the axiom audit.
- The former single-file development is `ObserverEquivariance/Core.lean`.
- Import structure (arrows mean "is imported by"):
  `Core` → `ProductModel`, `MinSpec`, `Examples/NonFaithful`, `Examples/Holonomy`;
  `MinSpec` → `MinSpecCorrespondence`, `NormalForm`;
  `MinSpecCorrespondence` → `BaseChange`;
  `NormalForm` → `LocalLifts`, `Descent`; `Descent` → `Residual` → `ResidualCategory`, `Calibration`;
  `LocalLifts` → `Components` → `Examples/TwoObject`;
  `BaseChange` + `Cocycles` → `BaseChangeCocycle`;
  `ProductModel` → `Examples/Twist`, `Examples/TwoObject`, `Examples/Records`;
  `Examples/Records` + `Calibration` → `Examples/RecordsCalibration`.
  `Cocycles` imports only mathlib; `AxiomAudit` imports only `Lean`.

## Intentional API changes

### Core

1. **Category instead of groupoid.** The global hypothesis `[Groupoid O]` is replaced by `[Category O]`.
   No general declaration assumes that `O` or `S` is a groupoid.
2. **Structure split.** `OEData G p` now `extends NormalizedPreDatum G p` (clauses (N1)–(N5) of
   `def:data`, without the invertibility part of (N5)) with the single extra field `p_faithful` ((N6)).
   The field list and field types are unchanged, and dot notation (`d.act`, `d.chi_comp`, …) and
   `where`-constructors work as before. Consequence: the generated projection constants are now named
   `NormalizedPreDatum.act`, …; fully qualified uses such as `OEData.act d` must be written `d.act`,
   and `OEData.mk` takes the pre-datum and `p_faithful`.
3. **Invertibility of the vertical arrows is derived, not assumed.** `OEData.ltrans_isIso` (instance)
   follows from `p_ltrans` and full faithfulness (`isFull` + `p_faithful`). `Λ`, `Λ_comp_p`,
   `idIsoΛ`, `ΛIsoId` use `inv (d.ltrans g x)` instead of `Groupoid.inv`. Added `OEData.ltransIso`
   (with `ltransIso_hom`, `ltransIso_inv`) and `OEData.p_map_inv_ltrans`.
4. **`OEData.base_hom_isIso` now carries an explicit groupoid hypothesis on `O`**
   (`hO : ∀ {x y : O} (f : x ⟶ y), IsIso f`), matching `rem:groupoid`; it is no longer a general
   theorem. Its converse is new: `OEData.hom_isIso_of_base_isIso` (hypothesis: every arrow of `S` is
   invertible).
5. New translation by an object function: `ΛFun d γ` with `ΛFun_comp_p`, `ΛFun_const`, `ΛFun_one`,
   `ΛFun_comp`, `ΛFun_isGEquivariant`, `ΛFun_preservesCleavage_iff`.
6. Paper-label references in Core comments were remapped to the new article
   (`def:oedata`→`def:data`, `def:autbox`→`def:lifts`, `thm:productnormalform`→`thm:normalform`,
   `cor:basegroupoid`→`rem:groupoid`, `thm:strict-classification`/`lem:rigidity`/`lem:canonical-lift`
   →`thm:strict`, `thm:theta-classification`→`thm:twisted`, `def:law-symmetry`/`cor:law`→`def:law`).
   Section numbers such as §4.1/§4.3 and the non-existent labels `sec:theta` and `ex:poincare` were
   replaced by labels (`sec:symmetries`, `thm:strict`, `thm:twisted`, `prop:cartesian`, `def:law`).
7. **`NormalizedPreDatum.act_free` is kept but marked REDUNDANT.** It is not a clause of `def:data`.
   It follows from `act_mul`, `base_coord` and `coord_base` (`lem:coordinates`), and this is proved
   in `OEData.coordinate_identities` (MinSpecCorrespondence). The field stays for API stability. It
   adds no hypothesis beyond `def:data`, and several Core proofs use it directly.
8. **`productNormalForm d : O ≌ S × Pair G` is kept as the weak (equivalence) form** of
   `thm:normalform`, for compatibility. Its docstring and the Core section header say so. The
   paper's strict isomorphism of categories is `normalFormTo_comp_normalFormFrom` /
   `normalFormFrom_comp_normalFormTo` in `NormalForm`.
9. Docstring-only corrections, no statement changed. The `IsGEquivariant` / `PreservesCleavage`
   docstrings cite `eq:equiv` / `eq:preserve` instead of "conditions (b)/(c)". The Poincaré/Lorentz
   "template" language is gone: `sec:scope` mentions `V ⋊ O(1,3)` only as an abstract shape, and
   nothing Lorentzian is formalized. `unbundled_lift_classification` now says that it quantifies over
   `S ≌ S` and yields bare functors, and that the group-level sequence is `Φ_surjective` /
   `ΛHom_injective` / `ker_Φ_eq_range_Λ`. `idIsoΛ` notes that injectivity of `ΛHom` needs
   `[Nonempty S]`. The Core witnesses are marked as different from `ex:twist`. The full-group
   `AutBoxGθ d θ` is described as the *analogue* of `H = ⊤`, not formally identified with it (see
   the last section).

Apart from these items and the additions listed under "New helper declarations in Core", every
declaration of the baseline file keeps its name and statement (up to `Groupoid O` → `Category O`).
This was checked by comparing the elaborated signatures of all shared constants when Core was
split out. The implementation reports state that all later Core edits were additions or docstring
changes.

### Deviations in the new modules (names and encodings)

10. **`OEData.IsInvariant d F`** (strict invariance `R_h ⋙ F = F`, `prop:residual`) is namespaced
    because mathlib already has a root `IsInvariant` (`Mathlib/Dynamics/Flow.lean`). Use it as
    `d.IsInvariant F`. A bare `IsInvariant d F` resolves to mathlib's definition. `IsInvariantNatTrans`
    stays at the root.
11. **`OEData.actFunctor_covers_id`** (Residual) has the same statement, `d.actFunctor h ⋙ p = p`,
    as `LocalLifts.actFunctor_comp_p` (note the namespace: there is no `OEData.actFunctor_comp_p`;
    the sibling in the minimal specification is `MinSpec.actFunctor_comp_p`). It gets its own name
    because Residual does not import
    LocalLifts, and the root file imports both, so one name in both modules would clash. Its docstring
    records the duplication.
12. **`IsVertical p v`** (`∃ h : p.obj x = p.obj y, p.map v = eqToHom h`) and its closure lemmas
    `IsVertical.id` / `eqToHom` / `comp` / `inv` live in `NormalForm`, not in Core. The definition
    follows the unlabeled paragraph right after `def:data`. It is neither `def:vertical-trivial` nor
    (N5), although both use it.
13. **`InvFun d C` and `InvFun.Hom` are structures** (fields `functor`/`invariant` and
    `nat`/`invariant`), not subtypes. A subtype wrapped in a `def` gave terms that are ill-typed at
    instance transparency, which broke `rw`/`simp`. Objects are still exactly the invariant functors
    and arrows exactly the invariant natural transformations.
14. The O-level residual action is the root `residualAction d F hF s : G →* Aut (F.obj (d.base s))`,
    built from the vertical arrows `OEData.vertArr` and `OEData.IsInvariant.residualHom`. An
    intermediate copy in namespace `Calibration` was removed before integration, and Calibration and
    RecordsCalibration use the root names.
15. `baseChange_twistFactor_mul` (BaseChange) is kept for backward compatibility. The canonical
    statement is `OECocycle.coboundary_mul`, and `baseChange_twistFactor_eq_coboundary`
    (BaseChangeCocycle) identifies the two by `rfl`.
16. `unrestricted_calibration_exists` keeps its existential statement. Its witness is exposed
    separately as `unrestrictedCalibration`; the existing theorem was not restated through it.
17. Local helper lemmas live in namespaces to avoid clashes: `ProductModel` (`productHom_ext`,
    `eqToHom_fst`, a global `@[simp]` lemma once imported), `LocalLifts`, `Components`,
    `AutEquivOver`, `ComponentsSwapExample`, `InvFun`, `ResidualCategory`, `Calibration`,
    `OECocycle`, `TwistExample`, `RecordsExample`, `RecordsCalibration`, `TwoObjectExample`,
    `NonFaithful`. The C₂ helpers (`c2Hom`, `c2MulEquiv`, `c2Gen`, …) exist twice, in `TwistExample`
    and `RecordsExample`, because Records may not import Twist. Holonomy has no namespace: its
    declarations are root-level, grouped in sections.
18. Some declarations take `(m : MinSpec G p)` or `(d : OEData G p)` as an explicit binder because
    their statement does not mention it (`MinSpec.hom_ext`, `MinSpec.no_strict_retraction`,
    `MinSpec.descent`, `OEData.descent`, `OEData.natTrans_descent`, …). Dot notation (`m.descent F`)
    still works.

## New helper declarations in Core (fix phase)

All of these were added after the review. They are additions only; no existing statement changed.

- **MulEquiv API for the four classification isomorphisms.** Each isomorphism was previously
  specified only by its type, which any abstract isomorphism satisfies. Each now has four `@[simp]`
  lemmas pinning the map to the paper's `(a, A) ↦ Λ_a Ã`:
  - `autBoxGMulEquivProd`: `autBoxGMulEquivProd_symm_apply` (`rfl`), `autBoxGMulEquivProd_apply_snd`
    (second component = `Φ`), `autBoxGMulEquivProd_ΛHom` (`ΛHom g ↦ (g, 1)`),
    `autBoxGMulEquivProd_liftHom` (`liftHom A ↦ (1, A)`);
  - `autBoxGOverMulEquivProd`: `autBoxGOverMulEquivProd_symm_apply`,
    `autBoxGOverMulEquivProd_apply_snd` (= `ΦOver`), `autBoxGOverMulEquivProd_ΛHomOver`,
    `autBoxGOverMulEquivProd_liftHomOver`;
  - `autBoxGθMulEquivSemidirect`: `autBoxGθMulEquivSemidirect_symm_apply`,
    `autBoxGθMulEquivSemidirect_apply_right` (= `Φθ`), `autBoxGθMulEquivSemidirect_ΛHomθ`
    (`↦ inl g`), `autBoxGθMulEquivSemidirect_liftHomθ` (`↦ inr A`);
  - `autBoxGθOverMulEquivSemidirect`: `autBoxGθOverMulEquivSemidirect_symm_apply`,
    `autBoxGθOverMulEquivSemidirect_apply_right` (= `ΦθOver`),
    `autBoxGθOverMulEquivSemidirect_ΛHomθOver`, `autBoxGθOverMulEquivSemidirect_liftHomθOver`.
- **`OEData.chi_split_cartesian`** (`prop:cartesian`, second sentence) bundles into one conjunction
  that every chosen `χ_{u,y}` is `IsCartesianOver` and that the splitting laws `reind_id`, `chi_id`,
  `reind_comp`, `chi_comp` hold. The fibration notion is this project's `IsCartesianOver` plus the
  chosen cleavage. No connection to mathlib's `Functor.IsFibered` is claimed.
- **Group-element form of the last sentence of `thm:strict`:**
  `existsUnique_ΛHom_mul_of_Φ_eq` (for `AutBoxG d`, hypothesis `Φ d e₁ = Φ d e₂`, conclusion
  `∃! g, e₂ = ΛHom d g * e₁`) and `existsUnique_ΛHomOver_mul_of_ΦOver_eq` (for `AutBoxGOver d H`).
  The twisted analogue is `existsUnique_ΛHomθOver_mul_of_ΦθOver_eq` (`thm:twisted`, unique
  factorization). Multiplication is `(e * e').hom = e'.hom ⋙ e.hom`, so `e₂ = Λ_g · e₁` is `rigidity`'s
  `F₂ = F₁ ⋙ Λ d g`. All three assume `[IsConnected S]`.
- **`autBoxGθOverOneMulEquiv d H : AutBoxGθOver d H 1 ≃* AutBoxGOver d H`** (remark after
  `thm:twisted`: the untwisted theorem is the case of trivial `θ`). It is the identity on `hom`, `inv`
  and the base, with `@[simp]` lemmas `autBoxGθOverOneMulEquiv_apply_hom` and
  `autBoxGθOverOneMulEquiv_apply_base`.
- **State stabilizer** (discussion after `def:law`): `stateStabilizer L σ : Subgroup (StrictAut S)`
  for a specified `MulAction (strictLawStabilizer L) X` and a state `σ : X`, defined as the image of
  `MulAction.stabilizer`; `mem_stateStabilizer_iff`, `stateStabilizer_le` (`H_{L,σ} ≤ H_L`), and
  `stateStabilizerAutBoxMulEquiv : AutBoxGOver d (stateStabilizer L σ) ≃* G × stateStabilizer L σ`
  for connected `S`, an instance of `autBoxGOverMulEquivProd`. The action of `H_L` on states is a
  hypothesis; the paper does not specify one.

## New modules

Each module's docstring lists the paper labels it covers and the declarations that formalize them.
The four modules adopted later (see "Adoption of the r4/r5 additions") carry shorter docstrings:
they name the label but not the declarations, and `Examples/RecordsR4.lean` names no label at all.
The paragraphs below name the principal ones.

**`ProductModel`** (`thm:normalform`, product side). `productData S G : OEData G (Prod.fst S (Pair G))`,
the canonical normalized datum on `S × Pair G` for an arbitrary base: action `(s, a) · h = (s, a h)`,
basepoints `(s, 1)`, transport `u^* y = (s, y₂)` with `χ = (u, *)`, and vertical arrows `(𝟙, *)`.
Simp lemmas `productData_act`, `productData_base`, `productData_reind`, `productData_chi`,
`productData_ltrans`, `productData_actFunctor`; the instance `isConnected_pair`. Twist, TwoObject and
Records use it; Holonomy does not (its transport is twisted by `ρ`).

**`MinSpec`** (`rem:audit`, forward part; `lem:coordinates`; `prop:fullness`). The structure
`MinSpec G p`: `p` full and faithful, plus a based object bijection `e : O ≃ S × G` whose first
component is `p.obj`. From `e` it derives basepoints, coordinates and the object action
(`MinSpec.coord_act_base`, `MinSpec.e_symm_eq`), the unique-lift API `MinSpec.liftOver`, the action
by functors `MinSpec.actFunctor`, and the forward map `OEData.toMinSpec` (with `full := d.isFull`).

**`MinSpecCorrespondence`** (`rem:audit`, converse and "each specification uniquely recovers the
other"; `lem:coordinates`). `MinSpec.toOEData` rebuilds a normalized datum, taking `χ` and `ℓ` as
unique lifts (`toOEData_chi_unique`, `toOEData_ltrans_unique`). The round trips
`MinSpec.toOEData_toMinSpec` and `OEData.toMinSpec_toOEData` are equalities of structures, packaged
as `oeDataEquivMinSpec : OEData G p ≃ MinSpec G p`. `OEData.ext_of_coord` says two normalized data
with the same coordinate function are equal; this is the Lean form of "(N3)–(N4) add no freely
variable transport data". Also `OEData.ext_of_data` (auxiliary), `OEData.coord_base_eq_one` and
`OEData.coordinate_identities` (freeness derived, not read off `act_free`). `OEData.toMinSpec_full`
and `MinSpec.toOEData_isFull` are proof-irrelevance sanity checks only.

**`NormalForm`** (`thm:normalform`, `cor:section`, `rem:groupoid`; vertical arrows from `sec:data`).
`IsVertical` and its closure lemmas. For `m : MinSpec G p`: `m.normalFormTo` and `m.normalFormFrom`
are strict inverse functors (`N ⋙ M = 𝟭`, `M ⋙ N = 𝟭` as functor equalities), both lying strictly
over `S` (`normalFormTo_comp_fst`, `MinSpec.normalFormFrom_comp_fst`). The `OEData` versions are
`normalFormTo_comp_normalFormFrom`, `normalFormFrom_comp_normalFormTo`, `normalFormFrom_comp_fst`,
`normalFormFrom_equivariant` and `normalFormTo_map_chi`. `StrictSection p` carries a strict
`B ⋙ p = 𝟭` and a vertical `η : p ⋙ B ≅ 𝟭`, with constructions `MinSpec.strictSection` and
`OEData.strictSection` (`B.obj s = b_s`, via `sectionFunctor`). `MinSpec.no_strict_retraction` shows
`p` is not a strict isomorphism when `G` is nontrivial and `S` nonempty. `MinSpec.base_hom_isIso` and
`MinSpec.hom_isIso_of_base_isIso` are the `MinSpec` forms of `rem:groupoid`.

**`LocalLifts`** (`lem:local`; the section formulation and the canonical-lift paragraph after it; the
proofs of `thm:strict` and `thm:twisted`). The multiplier `k = liftMultiplier d F` of an equivariant
functor over `A` (`lift_obj_eq`, `lift_obj_act_base`, `multiplier_unique`, `normalForm_lift_eq`). Arrows
are determined by the covering equation (`lift_map_eq_liftOver`, `lift_eq_of_obj_eq`), and transport
preservation holds iff `k` is constant along arrows (`preservesCleavage_iff_multiplier`). The converse
`liftByMultiplier` has a strict inverse (`liftByMultiplier_comp_inv`, `liftByMultiplier_inv_comp`),
giving `autBoxGOfMultiplier` / `autBoxGOverOfMultiplier`, and `eq_autBoxGOfMultiplier` shows every
`AutBoxG` element arises this way. On a connected base, `preservesCleavage_iff_exists_base_obj` and
`preservesCleavage_iff_exists_section` give the section form. `liftByMultiplier_one` and
`liftByMultiplier_const` handle the canonical lift, and `exists_unique_eq_liftFunctor_comp_Λ` the unique
factorization `Λ_a Ã`. Twisted analogues: `lift_obj_eq_twisted`, `multiplier_unique_twisted`,
`preservesCleavage_iff_multiplier_twisted`, `liftByMultiplierθ`, `autBoxGθOverOfMultiplier`,
`eq_liftByMultiplierθ`, `exists_unique_eq_liftFunctorθ_comp_Λ`. Core's rigidity internals are re-proved
as public lemmas (`liftMultiplier_eq_of_hom`, `liftMultiplier_const`).

**`Descent`** (`sec:descent`: `def:vertical-trivial`, `thm:descent`, `prop:weak-descent`,
`ex:invariant`). `SendsToIdentity` and `VerticallyTrivial p F`; clause (i) of the two-clause form is
redundant (`VerticallyTrivial.obj_eq_of_minSpec`, `verticallyTrivial_iff_two_clauses`). Strict
factorization for an arbitrary target `C`: `strictSection_descent`, `StrictSection.factor_eq`,
`StrictSection.factor_unique`, the bundled `strictSection_descent_factor` naming the factor `B ⋙ F`,
and `MinSpec.descent`, `OEData.descent`, `MinSpec.descent_factor`, `OEData.descent_factor`.
`StrictSection.descentEquiv` is only an object-level bijection. Natural transformations:
`natTrans_descent`, `natTrans_descent_of_eq` (paper form with `hE`, `hE'`, `α : F ⟶ F'`),
`StrictSection.descendNatTrans_app`, `StrictSection.natTrans_app_eq`. Weak descent for every `F`:
`weakDescentIso`, `weak_descent`. `ex:invariant`: `invariantPairFunctor`,
`invariantPairFunctor_not_verticallyTrivial`, `pairPUnit_functor_eq` (`Pair PUnit` is terminal).
Object functions: `MinSpec.objectFunction_descent`, `OEData.objectFunction_descent`.

**`Residual`** (`prop:residual` and the paragraph after it). `OEData.IsInvariant`,
`OEData.IsInvariant.obj_eq` / `map_eq`, `isInvariant_comp_p`, and `IsInvariantNatTrans` (closed under
`isInvariantNatTrans_id` / `_comp`). Product coordinates: `residualQ : S × Pair G ⥤ S × SingleObj G`
with `residualQ_invariant`; `productInvariant_iff_factors` (unique `F = Q ⋙ Ecal`, factor
`IsProductInvariant.factor`); `ResidualData S C G` and the equivalence
`functorProdBGEquivResidualData`; `productInvariant_iff_residualData`; the arrow formula
`residualQ_comp_toFunctor_map` / `IsProductInvariant.map_pairArr_residualData`; the descent criteria
`productDescent_iff_residual_trivial` and `IsProductInvariant.descent_iff`. On `O`:
`OEData.isInvariant_iff_isProductInvariant`, `invariant_iff_factors`, `OEData.vertArr`,
`residualAction` (`residualAction_hom`, `residualAction_eq_one_iff`, `residualAction_natural`,
`residualAction_agrees`), `OEData.IsInvariant.residualData`,
`OEData.IsInvariant.verticallyTrivial_iff_residualAction_trivial`,
`invariant_descends_iff_residual_trivial`, the O-level formula
`OEData.IsInvariant.map_eq_residualAction` / `map_eq_residualData`, the factorization
`OEData.IsInvariant.normalFormQ_comp_residualData`, and unique residual data
`invariant_iff_residualData` / `OEData.IsInvariant.residualData_unique`. For `ex:invariant`, the
residual action is the identity (`invariantPairFunctor_residualAction_hom`).

**`ResidualCategory`** (display after `prop:residual`:
`Fun_{G-inv}(O, C) ≅ Fun(S × BG, C) ≅ Fun(S, C^{BG})`). The category `InvFun d C` has invariant
functors as objects and invariant natural transformations as arrows. There is a strict isomorphism
`ResidualCategory.invFunToProdBG` / `ResidualCategory.prodBGToInvFun`, with both composites equal to
`𝟭` (`invFunToProdBG_comp_prodBGToInvFun`, `prodBGToInvFun_comp_invFunToProdBG`), followed by
mathlib's curry/uncurry (`curry_comp_uncurry_prodBG`, `uncurry_comp_curry_prodBG`).
`ResidualCategory.exists_not_isInvariantNatTrans` shows `InvFun` is not a full subcategory; the
witness needs a nonabelian `G`.

**`Calibration`** (`cor:invariant-calibration`, the paragraph before it and the discussion after it).
The paragraph before the corollary is covered in both directions:
`Calibration.residualAction_intertwines` (invariant transformations intertwine residual actions), and
the converse construction `Calibration.invariantNatTransOfResidual`, with
`Calibration.isInvariantNatTrans_invariantNatTransOfResidual`,
`Calibration.invariantNatTransOfResidual_app_base` and the iff
`Calibration.existsUnique_invariantNatTrans_iff`. The corollary itself is split into
`residualAction_trivial_of_invariant_iso` ((i)→(iii)), `invariant_iso_of_factors` ((ii)→(i)),
`residualAction_trivial_of_factors`, `verticallyTrivial_of_residualAction_trivial`, the iffs
`calibration_i_iff_ii`, `calibration_ii_iff_iii`, `calibration_i_iff_iii`, and the bundles
`invariant_calibration_tfae` (conjunction of iffs) and `invariant_calibration_list_tfae` (`List.TFAE`).
The discussion after it: `Calibration.action_trivial_iff_of_intertwining`,
`Calibration.residualAction_trivial_iff_of_invariant_iso`,
`no_invariant_calibration_of_residualAction_ne_one`, `unrestricted_calibration_exists` with witness
`unrestrictedCalibration`, and `unrestrictedCalibration_invariant_iff` (that calibration is invariant
iff every residual action is trivial).

**`Components`** (`prop:components`, `prop:nocleavage`, general part). No connectedness or nonemptiness
hypothesis. For components: `componentMap`, `componentPerm`, and
`componentAction H G : H →* MulAut (ConnectedComponents S → G)` (`componentAction_apply_eq_perm`). The
key identity `Ã Λ_δ Ã⁻¹ = Λ_{δ∘A⁻¹}` holds at functor level (`Components.liftFunctor_conj_ΛFun`,
`liftFunctor_conj_ΛFun_components`) and at group level (`liftHomOver_conj_components`). Multipliers
descend to components (`eq_of_zigzag_of_hom`, `liftMultiplier_factors_through_components`), the
factorization `F = Λ_γ Ã` is `liftByMultiplier_components_eq` / `autBoxGOverOfComponents_hom_eq`, and
the classification is
`autBoxGOverMulEquivComponents d H : AutBoxGOver d H ≃* (ConnectedComponents S → G) ⋊[componentAction H G] H`
with `autBoxGOverMulEquivComponents_symm_inr`. The remarks are covered by
`componentFunctions_unique_of_isEmpty`, `componentAction_eq_one`, `componentFunctionsMulEquiv` and
`autBoxGOverMulEquivProdOfComponents`. The swap example: `ComponentsSwapExample.componentAction_ne_one`,
`ComponentsSwapExample.componentAction_zpowers_ne_one`,
`ComponentsSwapExample.liftHomOver_discSwap_not_comm`. Unrestricted lifts: the group
`AutEquivOver d H`, `ΦEquivOver`, `objectAction`,
`autEquivOverMulEquiv d H : AutEquivOver d H ≃* (S → G) ⋊[objectAction H G] H`,
`kerΦEquivOverMulEquiv`, `autBoxGOverToAutEquivOver`, `autEquivOver_conj_object`,
`autEquivOverMulEquiv_symm_inr`, `autEquivOver_preservesCleavage_iff`,
`mem_range_autBoxGOverToAutEquivOver_iff`.

**`BaseChange`** (`prop:basechange`; group-level reading in `sec:normalization`). The rebased datum
`OEData.rebase d c` (`b'_s = b_s · c`, same action and transport; `rebase_one`, `rebase_rebase`).
Bare-family form on a connected base: `parallel_family_eq_translate` (`∃! c, ∀ s, b' s = b_s · c`) and
`parallel_family_eq_rebase_base`. Datum form: `parallel_basepoints_eq_rebase`, `eq_rebase_of_base`,
`exists_unique_eq_rebase`; `parallel_basepoints_const_unique` needs only `[Nonempty S]`. Functor
formulas: `coord_eq_of_base`, `Λ_eq_of_base`, `Λ_eq_conj_of_base`, `liftFunctor_eq_of_base`,
`liftFunctorθ_eq_of_base`, `liftFunctorθ_eq_conj_of_base`, `liftFunctorθ_obj_eq_of_base`. Group
level: the identity-on-`hom` identifications `autBoxGCongr`, `autBoxGOverCongr`, `autBoxGθOverCongr`;
`autBoxGθOverMulEquivSemidirect_symm_eq_of_base` and `autBoxGOverMulEquivProd_symm_eq_of_base` (the
identifications differ by conjugation with `Λ_c`); `liftHom_eq_of_base` and `liftHomOver_eq_of_base`
(the untwisted section is unchanged); `liftHomθOver_eq_of_base`.

**`Cocycles`** (cocycle paragraph of `sec:normalization`; pure group theory in namespace
`OECocycle`). Nonabelian cocycles `IsCocycle` and coboundaries `coboundary`, with `coboundary_mul` and
`cohomologous_one_coboundary`. `H1 θ` is a pointed set (`H1.trivialClass`, `H1.toPointed`). The
cocycle–section correspondence is `cocycleSectionEquiv`; cohomology is conjugation by `(c, 1)`
(`conj_inl_section`, `cohomologous_iff_sectionConj`). Classification: `H1EquivSectionClasses` (sections
of the fixed `G ⋊[θ] H` up to kernel conjugation), `section_range_isComplement`,
`sectionComplementEquiv`, `H1EquivComplementClasses`, and the basepoint lemmas
`H1EquivSectionClasses_trivialClass` and `H1EquivComplementClasses_trivialClass`. Extensions are not
classified; `G ⋊[θ] H` is fixed throughout.

**`BaseChangeCocycle`** (the remaining sentences after `prop:basechange`). `baseChange_twistFactor_eq_coboundary`;
`liftHomθOver_rebase_conj_ker` (the new canonical section is conjugate to the old one by one kernel
element, `Λ_c`, uniformly in `A`, without connectedness); `liftHomθOver_rebase_semidirect` (in the old
semidirect coordinates the new section is the cocycle section of `z_c`); the packaged
`liftHomθOverRebaseSection`; `liftHomθOver_rebase_sectionConj`; and `liftHomθOver_rebase_class` (its
class in `H¹(H,G)` is the trivial class).

**`AxiomAudit`** — two audit commands that fail the build on any axiom outside `propext`,
`Classical.choice`, `Quot.sound`:
`#assert_standard_axioms d₁ … dₙ` (named declarations; tested against `sorry`, a custom `axiom`,
and `native_decide`), and `#assert_standard_axioms_in_modules ObserverEquivariance`, which checks
every declaration — auxiliary `_proof_n`/`match_n` constants included — of every imported module
with that prefix (negative control: the same command on `Init.Prelude` fails on `sorryAx`).

**`Examples/Twist`** (`ex:twist`, instance of `thm:twisted`). Base `Pair (Fin 2)`, `G = G3`
(`Multiplicative (ZMod 3)`), `H = twistH = Subgroup.zpowers swapAut`, and the twist `twistθ` with
`twistθ_swap_apply` (`θ_A g = g⁻¹`) and `twistθ_ne_one`. Datum `twistData`, which is `productData`.
Lemmas: `swapAut_obj`, `twistLift_obj` (`(s, g) ↦ (A s, g⁻¹)`), `twistSemidirectH`, `twistSym`, and
`twistSymPerm` via `c3c2MulEquivS3` (`≅ S₃`), with `twistSymPerm_Λ_r` and `twistSymPerm_lift`. The
conjugation formula is `twist_conj` / `twist_conj_r`. The S₃ left/right illustration is
`s3_swap01_mul_swap12`, `s3_swap12_mul_swap01`, `s3_left_ne_right`, `s3_Λ_ne_actFunctor`. Core's older
`zmod3SemidirectWitness` is a different model and is unchanged.

**`Examples/TwoObject`** (the example after `prop:nocleavage`). Base `Fin 2` as a preorder category:
`arrow01`, `hom_subsingleton`, `hom_one_zero_isEmpty`, `arrow01_not_isIso`, `strictAut_eq_one`,
`top_eq_bot`. `G = C2`, `twoObjData = productData (Fin 2) C2`, `card_objects` (four objects). The
unrestricted kernel over the identity is `kerEquivProd : (ΦEquivOver twoObjData ⊤).ker ≃* C2 × C2`
(`kerEquivProd_symm_hom_obj`: independent fiber flips). The transport-preserving kernel is
`transportKerMulEquiv : (ΦOver twoObjData ⊤).ker ≃* C2`, via `transportKerToProd_range`
(= `diagSubgroup C2`). `flipOne_not_preservesCleavage` and `diagSubgroup_ne_top` show that the
restriction is proper. All names are in namespace `TwoObjectExample`.

**`Examples/NonFaithful`** (`ex:nonfaithful`). `nonfaithfulProj K : SingleObj K ⥤ Discrete PUnit`,
`nonfaithfulPreDatum K : NormalizedPreDatum PUnit (nonfaithfulProj K)`, and the instance
`nonfaithfulPreDatum_ltrans_isIso`. `nonfaithfulProj_not_faithful`, `nonfaithful_N1_N5_and_not_N6` and
`nonfaithful_isEmpty_OEData` show it is not an `OEData` for any presentation group. On the kernel side:
`IsNonfaithfulLift`, `nonfaithfulLiftKernel_eq_top`, `nonfaithfulLiftKernelEquiv : … ≃* MulAut K`,
`strictAut_discretePUnit_eq_one`, the object-level variant `IsNonfaithfulObjLift` with
`isNonfaithfulObjLift_iff`, `nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel` and
`nonfaithfulObjLiftKernelEquiv`. For `K = G3`: `nonfaithfulLiftKernelZMod3Equiv`,
`nat_card_nonfaithfulLiftKernel_G3`, `nonfaithful_kernel_not_presentationGroup`.

**`Examples/Holonomy`** (`sec:holonomy`, `prop:holonomy` and its two examples). The model
`HolTotal Γ G = SingleObj Γ × Pair G` with projection `holP` and ρ-twisted transport `holReind`,
`holChi`. Its laws: `holReind_id`, `holReind_comp`, `holChi_id`, `holChi_comp`, `holReind_act`,
`holChi_act`. `holonomy_N1_N2_N5_N6` bundles (N1), (N2), (N5), (N6), with `holLtrans_isIso`. (N4) holds
iff `ρ = 1` (`holReind_holBase_iff`), so `holonomy_not_normalized` and `holonomy_not_OEData` apply for
`ρ ≠ 1`. Lift group: `IsHolLift`, `HolLift ρ`, `IsHolLift.map_holChi`,
`holLiftEquiv : HolLift ρ ≃* Eρ ρ`. The extension: `Hρ` with `mem_Hρ_iff_conj`, `EρToHρ_surjective`,
`EρProjKerEquiv`, `holonomy_exact`, and on the lift group `holLiftProj`, `holLift_exact`,
`holLiftProjKerEquiv` (`≃* C_G(im ρ)`), `holLiftAut_one_mem_iff`. Special cases:
`holLiftEquivTrivial` (trivial `ρ`); the S₃ transposition `holS3CentralizerEquiv`,
`holS3_centralizer_ne_top`; `EρIdEquiv`, `Hρ_id`; the nonsplit Q₈ case `holQ8EρEquiv`, `holQ8HρEquiv`,
`holQ8_no_section`, `holQ8_orderOf_lift`, `holQ8KerEquiv`.

**`Examples/Records`** (`sec:records`, first half: base, law, presentations, base symmetry). `RecDom`
with `RecDom.isConnected` and `RecDom.not_isIso_fromFull_single`. Record spaces `recordSpace`,
restrictions `recRestrict`, law `L₀ τ`, `mem_recordSpace_full_iff` (needs `0 < τ`), `recordSpace_nontrivial`.
Signs `G = ℤˣ`, `recData = productData RecDom ℤˣ`. The symmetry: `recρ`, `recA`, `recH`,
`recHMulEquiv`, `recH_card`, `recLift_obj`, `recLift_comm_polarity`, `recSym` (`≅ C₂ × C₂`), and
`recSymProd`. The covariant implementation `recα : recA.hom ⋙ L₀ τ ≅ L₀ τ` has `recα_involution`. The
inequality `recA_comp_L₀_ne` (needs `τ ≠ 0`) gives `recA_not_mem_strictLawStabilizer_L₀` and
`recH_not_le_strictLawStabilizer_L₀`. Labeled level: `Lℓ τ = recLabel.prod' (L₀ τ)` with
`Lℓ_comp_snd`, `recA_comp_Lℓ_ne`, `strictLawStabilizer_Lℓ_eq_bot`, `recA_not_mem_strictLawStabilizer`,
`recαℓ`, `recαℓ_hom_app_snd`, `recαℓ_involution`.

**`Examples/RecordsCalibration`** (`sec:records`, second half). The raw-record functor `recD`
(`recD_map_apply`), `recD_isInvariant`, and its residual factor `recEcal` with
`residualQ_comp_recEcal`, `recEcal_unique`, `recEcal_residualData_E` (`E = L₀ τ`) and
`recEcal_residualData_σ_hom` (`σ_I(h) = h · id`). Also `recD_residualAction_hom`,
`recD_residualAction_ne_one`, `recD_map_vertical_neg` and `recD_not_factors`. The calibration `recC`:
`recC_naturality`, `recC_hom_app_act`, `recC_hom_app_act_neg_one`, `recC_hom_app_act_eq_neg`,
`recC_not_invariant`, `recD_invariantNatTrans_eq_zero`, `recD_no_invariant_iso`,
`recD_no_invariant_calibration`. The two information conditions: `recInfo_even`,
`recInfo_vertical_naturality_iff_even`, `recInfo_invariant_ne_id`, `recInfo_no_recovery_at`,
`recInfo_no_recovery`.

## Unresolved points and representation choices

The honest list INSTR §7 asks for. Part (a) is what is not formalized at all, with the reason
(out of scope, optional, or an open gap). Part (b) is what is formalized only partly or only in a
special case. Part (c) is the representation choices: places where a Lean statement has to be read
with care before it is taken as a statement about the paper.

### (a) Not formalized

1. **The interpretive sections.** `sec:introduction`, `sec:scope`, `sec:related` and `sec:lean`
   are out of scope: they are prose about motivation, physical reading and related literature, and
   they state no theorem. Nothing Lorentzian is formalized; `sec:scope` mentions `V ⋊ O(1,3)` only
   as an abstract shape. The formalization targets `sec:data` through `sec:boundaries`.
2. **The orbit-category remark** after `cor:invariant-calibration` ("the diagonal orbit category is
   `O/G ≅ S × BG` in the chosen coordinates"). Optional, and not an INSTR item. No quotient or
   orbit category is constructed anywhere. The closest formalized statements are
   `invariant_iff_factors` and `invariant_iff_residualData` (Residual) and the strict isomorphism
   `ResidualCategory.invFunToProdBG` / `prodBGToInvFun`. The module docstrings of `Residual`,
   `Calibration` and `ResidualCategory` mark the remark as deliberately omitted.
3. **The non-abelian-kernel remark** after the proof of `thm:strict`: the kernel need not be
   abelian, and a general lift `Λ_b Ã` need not commute with `Λ_a`. This is an **open gap**: no
   declaration states it. What exists is the positive half — `ΛHom_comm_liftHom`, which says that
   the *canonical* section centralizes the kernel, and a Core §10 comment recording that an
   arbitrary lift may carry a left translation and then conjugate `Λ` nontrivially when `G` is
   nonabelian. `ComponentsSwapExample.liftHomOver_discSwap_not_comm` is a genuine non-commutation
   witness, but a different one: it is about the component action over a disconnected base, not
   about a nonabelian `G`.
4. **The smooth-gauge comparison** in `sec:holonomy` (`Stab_Gau(P)(A) ≅ C_G(Hol_{u₀}(A))` for a
   connection on a principal bundle). Background drawn from the cited literature; INSTR says
   explicitly that it need not be formalized. Nothing about manifolds, connections or gauge groups
   appears in Lean. Its algebraic counterpart inside the model is `holLiftProjKerEquiv`
   (`ker holLiftProj ≃* C_G(im ρ)`) together with `holLiftAut_one_mem_iff`.
5. **The follow-up paragraph of `ex:nonfaithful`** (appending an extra `BK` factor to
   `S × Pair G`). No Lean. Open gap, small.
6. **Holonomy leftovers**, all known and small. The trivial-`ρ` case is only the abstract
   `holLiftEquivTrivial : HolLift 1 ≃* G × MulAut Γ`; it is not linked to
   `productData (SingleObj Γ) G` or to `autBoxGOverMulEquivProd`, and it is not stated to commute
   with the projections to the base. The Q₈ square relating `holQ8HρEquiv`, `EρToHρ` and
   `holQ8EρEquiv` is not stated, and there is no `HolLift`-level form of the no-section corollary.
   `IsHolLift` has the transport-arrow lemma `IsHolLift.map_holChi` but no morphism-level
   equivariance lemma (Core's `isGEquivariant_map_actHom` does not apply, since the holonomy model
   is not an `OEData`).
7. **Base change for the full-group twisted type.** `BaseChange` provides `autBoxGCongr`,
   `autBoxGOverCongr` and `autBoxGθOverCongr`, but nothing for `AutBoxGθ d θ` with
   `θ : StrictAut S →* MulAut G`, and no base-change form of `autBoxGθMulEquivSemidirect` or of
   `autBoxGMulEquivProd`. Mathematically this is the case `H = ⊤`; in Lean it is a different type.
8. **"The full-group `AutBoxGθ` is the case `H = ⊤`"** is not formalized, because the twist types
   differ (`θ : StrictAut S →* MulAut G` versus `θ : ↥⊤ →* MulAut G`). Only the other
   specialization in that remark is bridged at group level: `autBoxGθOverOneMulEquiv` identifies
   `AutBoxGθOver d H 1` with `AutBoxGOver d H`.
9. **No group-level twisted converse** matching the untwisted `eq_autBoxGOfMultiplier`. The twisted
   side has the constructor `autBoxGθOverOfMultiplier` and the functor-level `eq_liftByMultiplierθ`,
   but no bundled statement that every element of `AutBoxGθOver d H θ` arises from a multiplier.
   An asymmetry of the API, not an overclaim anywhere.
10. **No link to mathlib's fibration API.** `OEData.chi_split_cartesian` bundles the second sentence
    of `prop:cartesian` using this project's own `IsCartesianOver` together with the splitting laws.
    No connection to `Functor.IsPreFibered` / `Functor.IsFibered` is made, and its docstring says
    that none is claimed.
11. **`tab:assumptions`** has no declaration of its own, because it makes no theorem-level claim.
    Its checkable content is a property of the hypotheses elsewhere: no normal-form, section,
    descent, residual or calibration result carries `[IsConnected S]`. That connectedness appears
    only on `thm:strict`, `thm:twisted`, `prop:basechange` and the lemmas that need a single
    constant.

### (b) Formalized only partly, or only as a special case

1. **`prop:cartesian`, second sentence — stated, but in this project's vocabulary.** The
   mathematical content of the sentence is fully proved and bundled as one conjunction
   (`OEData.chi_split_cartesian`: every `χ_{u,y}` is `IsCartesianOver`, plus the four splitting
   laws), which is why `LEAN_COVERAGE.md` §2.2 marks the row verified. What is missing is only the
   connection to mathlib's vocabulary, as in (a) 10: a reader who wants "split Grothendieck
   fibration" in the sense of `Functor.IsFibered` does not get it from this development.
2. **"Naturality along vertical arrows is exactly the intertwining condition" — both directions,
   but in a particular shape.** The forward half is `Calibration.residualAction_intertwines`. The
   converse is `Calibration.invariantNatTransOfResidual` with
   `Calibration.isInvariantNatTrans_invariantNatTransOfResidual`, and the two are packaged as
   `Calibration.existsUnique_invariantNatTrans_iff`. That iff is stated about a *basepoint family*
   `β`: an invariant transformation with `α.app (b_s) = β s` exists uniquely iff `β` is natural
   along the section arrows `B(u)` and intertwines the residual actions. It is not a bare
   biconditional about transformations; the naive form would be trivial, since intertwining follows
   from fiber constancy.
3. **"An unrestricted calibration exists but need not be invariant" — general; "it can identify
   functors with different residual actions" — special case only.** The general half is
   `unrestrictedCalibration` together with `unrestrictedCalibration_invariant_iff` (invariant iff
   every residual action is trivial). The stronger reading, that an unrestricted natural isomorphism
   identifies functors with genuinely different residual actions, is formalized **only** as the
   records instance: `recC`, `recC_not_invariant`, `recD_residualAction_ne_one`,
   `recD_no_invariant_iso`, `recD_no_invariant_calibration`.
4. **`ResidualCategory.exists_not_isInvariantNatTrans` uses a different witness from the paper's.**
   The Lean witness is a non-invariant automorphism of a single functor and needs a **nonabelian**
   `G`. The paper makes the same point with the `sec:records` calibration, where `G = ℤˣ` is
   abelian. Both are formalized, but they are not the same example; the docstrings say so and
   cross-reference the records file.
5. **Disconnected bases — the remark is witnessed, but not in its strongest reading.**
   `ComponentsSwapExample` proves that the component action is nontrivial
   (`componentAction_ne_one`, `componentAction_zpowers_ne_one`) and that the canonical lift of the
   swap fails to commute with a componentwise translation (`liftHomOver_discSwap_not_comm`). It does
   **not** prove that the resulting semidirect product is abstractly non-isomorphic to some direct
   product. The paper does not claim that either, but the distinction is worth stating.
6. **`ex:nonfaithful` — the kernel is cut out differently from the paper, though the difference is
   now bounded.** It is a subgroup of `StrictAut (SingleObj K)` satisfying the lift conditions over
   `A = 𝟭`, not the kernel of a projection `Φ : Sym_H(p) → H` from a group of pairs `(F, A)`; that
   group of pairs is not built. The predicate `IsNonfaithfulLift` is also stronger than `def:lifts`
   (it adds arrow-level equivariance, the χ equation and ℓ-preservation). Both points are contained:
   `IsNonfaithfulObjLift` has exactly the object-level conditions of `def:lifts`,
   `isNonfaithfulObjLift_iff` shows the two predicates agree,
   `nonfaithfulObjLiftKernel_eq_nonfaithfulLiftKernel` identifies the two kernels, and
   `strictAut_discretePUnit_eq_one` shows every strict base automorphism is trivial — so the
   subgroup really is the whole kernel, and `nonfaithfulLiftKernelEquiv : … ≃* MulAut K` carries
   over to the paper's kernel.
7. **Records, labeled level — true but uninformative about the law.**
   `recA_not_mem_strictLawStabilizer` and `strictLawStabilizer_Lℓ_eq_bot` are proved from the labels
   and the thinness of the base alone. The same proof applies verbatim to *any* functor
   `I ↦ (⟨I⟩, V(I))`, whatever the law, so at the labeled level these statements say nothing about
   the free-particle law. The informative statement is the unlabeled `recA_comp_L₀_ne`; see (c) 1.
8. **Transport preservation in section form — existence only.**
   `preservesCleavage_iff_exists_base_obj` and `preservesCleavage_iff_exists_section` give the
   existence of the element `c`. Uniqueness, which does hold by freeness together with
   connectedness, is not stated. Optional strengthening.
9. **`StrictSection.descentEquiv` is an object-level bijection only.** The morphism half of the
   paper's "universal strict passage" is `natTrans_descent` / `natTrans_descent_of_eq`; the
   docstring now says this rather than crediting the bijection with the whole claim.
10. **`productNormalForm` is the weak (equivalence) form** of `thm:normalform`, kept for
    compatibility; the paper's strict isomorphism of categories is proved separately. See
    "Intentional API changes" item 8, and (c) 8 below.
11. **`unrestricted_calibration_exists` remains an existential.** Its witness is available
    separately as `unrestrictedCalibration`, but the theorem was not restated through it, so its
    statement alone does not name the witness.

### (c) Representation choices

1. **Labeled and unlabeled record spaces (`sec:records`).** Both encodings are kept, and they carry
   different weight.
   - *Unlabeled.* `L₀ τ : RecDom ⥤ ModuleCat.{0} ℝ` is the paper's `L`. Here `LA ≠ L` is the
     informative statement, and it is now proved: `recA_comp_L₀_ne (τ) (hτ : τ ≠ 0) :
     recA.hom ⋙ L₀ τ ≠ L₀ τ`. The proof evaluates on the index record `recIdxRecord` and uses that
     the `eqToHom` casts are morphisms of `ModuleCat ℝ`, hence linear
     (`L₀_eqToHom_hom_apply_of_eq`) — no equality of carrier types is needed. Corollaries:
     `recA_not_mem_strictLawStabilizer_L₀`, `recH_not_le_strictLawStabilizer_L₀`.
   - *Labeled.* `Lℓ τ = recLabel.prod' (L₀ τ) : RecDom ⥤ Pair RecDom × ModuleCat.{0} ℝ` is the
     literal reading of "explicitly labeled vector spaces": the label of `L(I)` is its observation
     domain. The label factor `Pair RecDom` has exactly one arrow between any two objects, so it
     adds no morphism data, and forgetting labels gives back the unlabeled law
     (`Lℓ_comp_snd : Lℓ τ ⋙ Prod.snd = L₀ τ`, by `rfl`). At this level the inequality follows
     from the labels alone, and the triviality of the strict stabilizer from the labels together
     with the thinness of the base — see (b) 7.
2. **The parameter `τ`.** The membership characterization `mem_recordSpace_full_iff` needs `0 < τ`.
   The law inequality needs only `τ ≠ 0`, and is stated that way. The case `τ = 0` is not stated:
   it would require deciding an equality of carrier types, which Lean cannot do here.
3. **Signs as `G = ℤˣ`**, acting on real vector spaces by `((ε : ℤ) : ℝ) • ·`, with
   `recData = productData RecDom ℤˣ`. The sign group is represented exactly, not as an abstract
   `C₂`, so that the action on records is definitional.
4. **`Pair PUnit` as the terminal base** in `ex:invariant`, where the paper writes `*`. That it is
   terminal is proved, not assumed: `pairPUnit_obj_eq` (any two objects are equal) and
   `pairPUnit_functor_eq` (any two functors into it are equal).
5. **`Fin 2` with its preorder category structure** as the two-object base of the example after
   `prop:nocleavage`: one nonidentity arrow (`arrow01`), hom-sets subsingleton
   (`hom_subsingleton`), no arrow backwards (`hom_one_zero_isEmpty`), and `arrow01_not_isIso`.
   Consequently `StrictAut (Fin 2)` is trivial (`strictAut_eq_one`) and `H = ⊤ = ⊥` (`top_eq_bot`)
   is the only possible base subgroup, so the example isolates the vertical phenomenon.
6. **`NormalizedPreDatum` carries (N1)–(N5) *without* the invertibility part of (N5)**: `ltrans` is
   only a vertical arrow there. Invertibility is derived once (N6) is available
   (`OEData.ltrans_isIso`). So `NormalizedPreDatum` alone is strictly weaker than the paper's
   (N1)–(N5), and `Examples/NonFaithful` depends on exactly that: `nonfaithfulPreDatum` is a
   pre-datum, and invertibility of ℓ is a separate instance.
7. **`NormalizedPreDatum.act_free` is kept although it is redundant**, for API stability; it adds no
   hypothesis beyond `def:data`. See "Intentional API changes" item 7.
8. **`productNormalForm` is kept in its weak (equivalence) form**, with the strict isomorphism
   proved separately. See "Intentional API changes" item 8.
9. **Universes.** The `Groupoid` instance on `Pair X` has `Hom _ _ := PUnit` with a *free* universe.
   The hom universe of `HolTotal Γ G = SingleObj Γ × Pair G` is therefore an extra free parameter,
   and a bare reference to a lemma about it can leave universe metavariables. Three proofs work
   around this without changing any statement: the holonomy bundle inlines two proofs,
   `holonomy_not_OEData` repeats the argument of `holonomy_not_normalized` instead of invoking it,
   and `swapAut_obj` is proved by `⟨rfl, rfl⟩` rather than by pairing its two component lemmas.
   Pinning the universe (`Hom _ _ := PUnit.{1}`) would remove the quirk, but it changes Core and was
   not done. Separately, `Examples/NonFaithful` fixes `PUnit.{1}` (`Discrete PUnit.{1}`, and
   `nonfaithfulPreDatum K : NormalizedPreDatum PUnit.{1} _`) while `K` stays universe-polymorphic;
   this rules out a presentation group `PUnit.{u+1}` living in `K`'s universe. Cosmetic, and not
   generalized.
10. **Multiplication order.** In `AutBoxG`, `AutBoxGOver` and `AutEquivOver`,
    `(e * e').hom = e'.hom ⋙ e.hom`. So `e₂ = Λ_g · e₁` in `existsUnique_ΛHom_mul_of_Φ_eq` is
    `rigidity`'s `F₂ = F₁ ⋙ Λ d g`, and the paper's `Ã Λ_δ Ã⁻¹` has underlying functor
    `liftFunctor A.inv ⋙ ΛFun δ ⋙ liftFunctor A.hom`. In `SingleObj`, composition is `f ≫ g = g * f`
    (multiplication in operator order), as in the paper.
11. **Structures rather than subtypes** for `InvFun` and `InvFun.Hom`, and explicit `(d : OEData …)`
    / `(m : MinSpec …)` binders on statements that do not mention the datum, are representation
    choices too; they are recorded under "Deviations in the new modules", items 13 and 18.

## Deliverables

- **`ObserverEquivariance.lean`** — the entry point: it imports every module and runs
  `#assert_standard_axioms_in_modules ObserverEquivariance`. (It imported the 21 modules of this
  revision; it now imports 25 — see "Adoption of the r4/r5 additions".) Its header comment was
  rewritten for
  this revision (INSTR §7): the r2 title and source file, the `sec:data`–`sec:boundaries` label
  scheme, a scope note, the context and the exact carriers of `[IsConnected S]` / `[Nonempty S]`,
  a module map for all 21 modules, and a declaration directory per paper label replacing the old
  concordance block. Every stale label of the earlier draft is gone, and `rem:groupoid` is stated
  with its explicit groupoid hypothesis. The older `#print axioms` block is retained below the
  header, marked as inherited from the archived groupoid snapshot; the executable
  `#assert_standard_axioms_in_modules` check is the authoritative one.
- **The 21 modules** under `ObserverEquivariance/`: `Core`, `ProductModel`, `MinSpec`,
  `MinSpecCorrespondence`, `NormalForm`, `Descent`, `Residual`, `ResidualCategory`, `Calibration`,
  `LocalLifts`, `BaseChange`, `Cocycles`, `BaseChangeCocycle`, `Components`, `AxiomAudit`, and
  `Examples/{Twist, TwoObject, NonFaithful, Holonomy, Records, RecordsCalibration}`.
  Four more were added later, bringing the total to **25**: `Comparisons`, `Implementations`,
  `Examples/ComplexObstruction` and `Examples/RecordsR4` — see "Adoption of the r4/r5 additions".
- **`LEAN_COVERAGE.md`** — the coverage matrix required by INSTR §7, complete: §1 (scope,
  environment, reproduction, status legend, conventions), §2.1–§2.7 (one row per item of
  `sec:data` through `sec:boundaries`, including the claims INSTR lists separately), §3 (out of
  scope, remarks with no Lean statement, the `partial` rows, statements narrower than the prose,
  gaps closed after the review pass, documentation debt) and §4 (representation choices).
- **`CHANGES.md`** — this file: what changed, why, and the list above.
- **`scripts/audit.sh`** — the reproducible build and audit. It strips comments before scanning for
  `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` / `implemented_by`, runs `lake build`,
  writes the raw log (default `BUILD_LOG_RAW.txt`), and exits non-zero if the build fails, if a
  forbidden construct occurs in Lean code, or if the module-wide axiom audit did not run.
- **`BUILD_LOG.txt`** — the build and audit log of the current tree (2026-09-25; see "Article
  revision r6 and release build"): environment,
  exact commands, the git blob SHA-1 and line count of every source file as built, the
  forbidden-construct scan, `lake build` (2272 jobs, exit 0) and the executable audit line for all
  2766 declarations in 25 modules, plus the retained 18 `#print axioms` diagnostics and, separately, the baseline
  run of the pre-revision file. The archived 20 August 2026 log of the single-file development is
  preserved in git history at commit `f3f9182`; the two runs certify nothing about each other.
  `scripts/audit.sh` regenerates the raw log (`BUILD_LOG_RAW.txt`) on demand. The 8518-job /
  2599-declaration figures are those of **this** revision; the current tree builds in 2272 jobs and
  audits 2766 declarations in 25 modules — see "Adoption of the r4/r5 additions" for why the
  declaration count moves with the import surface.
- **The reproducible project files** — `lakefile.lean`, `lean-toolchain`
  (`leanprover/lean4:v4.31.0-rc1`) and `lake-manifest.json` (mathlib
  `8834d3761934044a64c98afb757c1673fad03521`), unchanged by this revision. This revision's
  reference paper was r2 (`perspectives_invariance_calibration_2026-09-05_r2.tex`), which, like
  every manuscript source, is kept outside this repository. The pins are still unchanged; the
  current reference paper is revision r6 (see the last section).

## Adoption of the r4/r5 additions (21 September 2026)

Everything above documents the r2 revision and still describes it. This section records a later,
separate event: the adoption of an **external contribution** into this repository, and the figures
that the article's revision r5 cites.

Reference paper from here on: `perspectives_invariance_calibration_2026-09-19_r5.tex`
(kept outside this repository; r5, 19 September 2026, *Symmetry Between Perspectives: Invariant Calibration and Symmetry Lifts*).
Relative to r3 it adds the labels `prop:comparisons`, `prop:data-implementation`,
`ex:complex-obstruction`, `sec:implementation`, `eq:implementation-intertwiner`,
`tab:recovery-tasks`, and `sec:lean-r5` (replacing `sec:lean-r4`). Every pre-existing statement and
label is unchanged from r2/r3, so nothing above is invalidated by the new revision.

### Provenance

The additions arrived as `doc/ObserverEquivariance_r4.zip` (kept outside this repository), produced
by an outside agent that had
been given this repository's 22 Lean files but not the repository itself. It is an **extension** of
this development, not a rewrite. Comparing the archive's Lean sources with this repository as it
stood before the adoption (commit `30ba4fd`), over the 22 pre-existing Lean files:

- **17 of the 21 pre-existing modules are byte-identical**;
- four modules are new (`Comparisons`, `Implementations`, `Examples/ComplexObstruction`,
  `Examples/RecordsR4`);
- four modules differ **only in their `import` lines** — `Core`, `Cocycles`, `ResidualCategory`,
  `Examples/Twist` — plus one comment in `Core.lean` (see below);
- the entry file `ObserverEquivariance.lean` differs in its imports *and* carries a rewritten r4
  header in the archive. Only the four added import lines were taken; the header was rewritten
  separately against r5, not copied from the archive.

No pre-existing statement, proof body, docstring or declaration name was changed by the archive.
None of the four new modules contains `sorry`, `admit`, `axiom` or `native_decide`.

### What was adopted

**1. Four new modules, copied in verbatim.**

| module | lines | principal paper label |
| --- | --- | --- |
| `ObserverEquivariance/Comparisons.lean` | 212 | `prop:comparisons` |
| `ObserverEquivariance/Implementations.lean` | 130 | `prop:data-implementation`, `sec:implementation`, `eq:implementation-intertwiner` |
| `ObserverEquivariance/Examples/ComplexObstruction.lean` | 283 | `ex:complex-obstruction` |
| `ObserverEquivariance/Examples/RecordsR4.lean` | 218 | `sec:records` additions, `tab:recovery-tasks` |

Import positions: `Calibration` + `ProductModel` → `Comparisons` → `Implementations`
(also importing `LocalLifts`); `Implementations` + `Examples/Twist` →
`Examples/ComplexObstruction`; `Examples/RecordsCalibration` → `Examples/RecordsR4`.

**2. The narrowed imports** of `Core`, `Cocycles`, `ResidualCategory` and `Examples/Twist`
(see "Import narrowing" below).

**3. Nothing else.** See "What was not adopted".

### The four new modules

All declarations of `Comparisons` and `Implementations` live in namespace `ResidualData`, so they
are reached by dot notation on the existing `ResidualData S C G` of `Residual`. The two general
modules are stated **in the strict product normal form** (base `S × Pair G`, datum
`productData S G`), for an arbitrary base category `S` and an arbitrary target `C`; they are not
separately restated for an arbitrary normalized datum, the passage being the inherited normal-form
and residual-data theorems.

**`Comparisons`** (`prop:comparisons`). The presentation functor of base data is the abbreviation
`ResidualData.presentationFunctor D = residualQ S G ⋙ D.toFunctor` — the existing functor, not a
new hypothesis — with `presentation_map_section`, `presentation_map_vertical` and
`presentationFunctor_isInvariant`. `presentationIso` exhibits the unrestricted comparison
`Prod.fst S (Pair G) ⋙ D.E ≅ D.presentationFunctor` with components `σ_s(a)`. The extension and
restriction maps are `comparison` (from a base transformation `β : D.E ⟶ D'.E`, with no
intertwining assumption) and `restrictComparison` (evaluation at the chosen section `(s, 1)`,
`comparison_app_residual` giving the component formula); they are mutually inverse, packaged as the
bijection `comparisonEquiv D D' : (D.presentationFunctor ⟶ D'.presentationFunctor) ≃ (D.E ⟶ D'.E)`,
with the isomorphism versions `comparisonIso` and `restrictComparisonIso`. Invertibility is
detected on the section (`isIso_comparison_iff`). Invariance is exactly independence of the
presentation coordinate (`invariant_iff_constant`), and under the bijection it is exactly the
intertwining condition (`comparison_invariant_iff`). Prescribed targets use the trivial data
`ResidualData.trivial L` (`trivial_presentationFunctor`): `prescribed_iso_iff` says unrestricted
calibration to `p ⋙ L` holds iff `D.E ≅ L`, and `prescribed_invariant_iso_iff` says the invariant
version holds iff additionally every `D.σ s = 1`.

**`Implementations`** (`prop:data-implementation`, `sec:implementation`,
`eq:implementation-intertwiner`). `ResidualData.twisted D A θ` pulls residual data back along a
base functor `A` and a fibre automorphism `θ`. `canonical_product_lift_eq` identifies the existing
canonical twisted lift with the product formula
(`liftFunctorθ (productData S G) A θ = multiplierProductFunctorθ A θ (fun _ => 1)`), including its
action on arrows, and `twisted_presentationFunctor` /
`liftFunctorθ_comp_presentationFunctor` compute the residual data after that lift. The two sides of
the criterion are `InvariantImplementation D A θ` (an invariant natural isomorphism
`(D.twisted A θ).presentationFunctor ≅ D.presentationFunctor`) and `TwistedIntertwiner D A θ` (an
iso `A ⋙ D.E ≅ D.E` satisfying the twisted intertwining equations, i.e.
`eq:implementation-intertwiner`); `implementationEquiv` is the bijection between them,
`implementation_app` records that an invariant implementation has coordinate-independent
components, and `invariant_implementation_iff` is the existence form. The criterion concerns **one**
selected base transformation and asserts no automatic coherence for a group-indexed family. Finally
`multiplier_product_lift_eq` and, for an abelian presentation group,
`translated_twisted_presentationFunctor` / `translated_lift_comp_presentationFunctor` show that
constant fibre translations leave the residual data unchanged.

**`Examples/ComplexObstruction`** (`ex:complex-obstruction`, namespace `ComplexObstruction`). Built
on the existing `C₃`, base interchange and inversion twist of `Examples/Twist`, with the actual
character generated by `e^{2πi/3}`: `omega`, `omega_primitive`, `omega_pow_three`, `omega_inv_ne`,
the unit `omegaUnit`, `intCharacter` and `character : G3 →* ℂˣ`, then `scalarRepresentation` and
`representation : G3 →* Aut (ModuleCat.of ℂ ℂ)`. The data are `complexData` with presentation
functor `F` and `F_isInvariant`. The obstruction is `no_invariant_complex_implementation` (the
canonical inversion-twisted lift admits no invariant complex-linear implementation, via
`intertwiner_eq_zero`: a complex-linear intertwiner between the inverse character and the original
is zero), strengthened to **every** transport-preserving inversion-twisted lift over the
interchange by `no_invariant_complex_implementation_any_lift`, which takes
`IsTwistedEquivariant twistData (twistθ twistHSwap) T` and `PreservesCleavage twistData T
swapFunctor` and uses the existing classification. The unrestricted comparison exists
(`unrestrictedImplementation`, `unrestrictedImplementation_app`: components `χ(g)² · z`) and is not
invariant (`unrestrictedImplementation_not_invariant`). Realification is restriction of scalars
(`realification`, `realData`, `realData_presentationFunctor`); there the conjugation
`conjugationIso` becomes admissible (`omega_conj`, `character_conj`, `real_intertwines`), giving the
invariant `realImplementation` with `realImplementation_app` (componentwise `starRingEnd ℂ`) and the
involution equations `conjugation_involution`, `realImplementation_involution`.

**`Examples/RecordsR4`** (additional measurement calculations for `sec:records`;
`tab:recovery-tasks`; namespace `RecordsR4`). Procedures are `Procedure τ` with the two separate
conditions `IsEven` and `RespectsRestrictions`. Counterexamples: `identity_not_even`, and
`maxProcedure` (`max |y_j| · 1`), which is even (`maxProcedure_even`) but does not commute with
restriction (`maxProcedure_not_natural`, needing `τ ≠ 0`). The set-valued sign-orbit target is
`signSetoid` / `SignOrbit` / `orbitClass` (`orbitClass_eq_iff`), `orbitMap` and the functor
`orbitFunctor τ : RecDom ⥤ Type`, with `orbitClass_sign`; recovery from raw records is the natural
transformation `orbitRecovery τ : recD τ ⋙ forget (ModuleCat ℝ) ⟶ recP ⋙ orbitFunctor τ`, and it
**is** invariant (`orbitRecovery_invariant`) — the contrast to the linear case. Linear coinvariants
of the sign action vanish: `signRelations`, `signRelations_eq_top`, `linear_coinvariants_zero`,
`linear_coinvariants_subsingleton`. A nonzero reference observation recovers the sign and the value
exactly, as scalar identities in `ℝ` (`reference_determines_sign`, `reference_recovers_value`);
nothing is stated at the level of the record functors. Time reflection on trajectory
parameters is `reflectTrajectory` with `reflectTrajectory_involution` and the fixed-point criterion
`reflectTrajectory_fixed_iff` (`v = 0`); `trajectoryRecord` and `recα_trajectory` link the parameter
calculation explicitly to the inherited natural time-reversal map `recα` of `Examples/Records`.

### Import narrowing

The blanket `import Mathlib` is gone from the project: `grep -rn '^import Mathlib$'` over
`ObserverEquivariance.lean` and `ObserverEquivariance/` now returns nothing. Four modules changed,
and **only their import lines** (plus the `Core` comment treated in the next subsection):

- **`Core`** — `import Mathlib` replaced by 17 explicit imports:
  `Mathlib.CategoryTheory.{ConnectedComponents, SingleObj, Products.Basic, Pi.Basic}`,
  `Mathlib.Algebra.Category.ModuleCat.Basic`,
  `Mathlib.GroupTheory.{SemidirectProduct, SpecificGroups.Quaternion, Perm.Fin}`,
  `Mathlib.Data.{ZMod.Basic, Real.Basic}`, `Mathlib.RingTheory.RootsOfUnity.Complex`, and
  `Mathlib.Tactic.{Group, FinCases, NormNum, LinearCombination, Linarith, TFAE}`.
- **`Cocycles`** — `import Mathlib` replaced by `Mathlib.GroupTheory.SemidirectProduct`,
  `Mathlib.Tactic.Group`, `Mathlib.CategoryTheory.Category.Pointed`.
- **`ResidualCategory`** — one import *added*, `Mathlib.CategoryTheory.Functor.Currying`.
- **`Examples/Twist`** — one import *added*, `Mathlib.GroupTheory.Perm.Cycle.Concrete`.

The last two never carried a blanket import themselves; they had been receiving all of mathlib
transitively through `Core`, and needed one named file each once `Core` stopped supplying it. Every
other module's import line is unchanged. No statement, proof body, docstring or declaration name was
touched: this was verified by diffing the repository against the archive file by file. After the
adoption, all 25 modules are byte-identical to the archive except `Core.lean`, which differs only
in the comment treated below.

**Effect.** `lake build` is now **2272 jobs** instead of 8518 — a much smaller reproduction
footprint for anyone rebuilding the development from the pinned mathlib.

### The twisted-conjugation comment

The archive's `Core.lean` had **reverted** an earlier correction of this repository's: the §14
comment on twisted equivariance, which states the conjugation identities in Lean's diagrammatic
order (`(liftFunctor A)⁻¹ ⋙ Λ d g ⋙ liftFunctor A = Λ d g`, i.e. `Ã Λ_g Ã⁻¹ = Λ_g` in operator
order; and `(liftFunctorθ A θ)⁻¹ ⋙ Λ d g ⋙ liftFunctorθ A θ = Λ d (θ g)`, operator order
`Ã Λ_g Ã⁻¹ = Λ_{θ g}`, `Λ_comp_liftθ`). The correction was **re-applied on top of** the narrowed
imports, so `Core.lean` now carries both changes. The comment is correct in the repository; it is
only the archive copy that is stale.

### New figures

Verified by `scripts/audit.sh` (exit 0) on 21 September 2026, environment pins unchanged
(`lean-toolchain` = `leanprover/lean4:v4.31.0-rc1`, mathlib
`8834d3761934044a64c98afb757c1673fad03521`):

- `lake build` green, **2272 jobs**, no errors and no warnings;
- the source scan finds no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `implemented_by`
  in Lean code;
- `#assert_standard_axioms_in_modules ObserverEquivariance` reports that all **2766 declarations in
  25 modules** depend only on `propext`, `Classical.choice` and `Quot.sound`.

**On the declaration count.** It is not a stable invariant of the mathematics. The same source tree
with the old blanket imports reported **2761** declarations in 8518 jobs; with the narrowed imports
it reports 2766. The command counts every declaration of every imported `ObserverEquivariance.*`
module, auxiliary `_proof_n` / `match_n` constants included, and which auxiliary constants are
generated depends on the instances and simp lemmas in scope — that is, on the import surface. The
difference is an artefact of elaboration, not of added or removed content. **2766 declarations in
25 modules** is what article revision r5 cites (`sec:lean`); the **2272 jobs** are this
repository's own figure, which revision r5 does not quote and revision r6 does. Both are what this
repository now produces.

### What was not adopted

The archive also carried its own project scaffolding, describing its own layout rather than this
one. None of it was taken:

- `lakefile.toml` — this repository keeps `lakefile.lean`;
- `scripts/audit.py` and `scripts/fetch_cache.py` — this repository keeps the bash
  `scripts/audit.sh`, which is what produced the figures above;
- the archive's `README.md`, `CHANGES.md`, `LEAN_COVERAGE.md` and `BUILD_LOG.txt` — this repository
  keeps its own, which are longer and more precise and whose counts describe this layout;
- the archive's rewritten header for `ObserverEquivariance.lean`, which is written against r4 and
  cites the archive's own layout and figures. Only its four new `import` lines were taken.

The archive's documents were read as a starting point only. Every claim in this section was checked
against the actual source in this repository.

## Article revision r6 and release build (25 September 2026)

Reference paper from here on: revision r6 of 25 September 2026,
`perspectives_invariance_calibration_2026-09-25_r6.tex` (distributed with the article, not with
this repository). r6 is an editorial revision of r5. It revises the abstract, the introduction,
the conclusion and the account of the formalization in `sec:lean`, and in `ex:complex-obstruction`
it replaces "apply the forgetful functor to Vect_ℝ" with "restrict scalars to ℝ", which is what
`realification` does. No mathematical statement and no LaTeX label changed: the label sets of r5
and r6 are identical (57 labels), so every label cited in this repository resolves in both.

### What changed in the repository

Only comments, the companion documents and the audit script changed. No statement, proof, import
or declaration name changed.

- `ObserverEquivariance.lean`, header comment: it names r6 as the reference manuscript. It no longer
  states the date of the recorded run, which is now given only in `BUILD_LOG.txt`, so the header
  does not have to change with each release. The gloss on the labeled `LA ≠ L` now says that
  `strictLawStabilizer_Lℓ_eq_bot` is proved for `Lℓ τ` and that the same argument would apply to
  any labeled functor of this form. The declaration directory lists `MinSpec.no_strict_retraction`
  as a result beyond `cor:section`, which asserts only that `p` is an equivalence.
- `Comparisons.lean`, `Implementations.lean`, `Examples/ComplexObstruction.lean`,
  `Examples/RecordsR4.lean`: the docstrings name article revision r5 instead of the draft
  designation r4. The module name `RecordsR4` is kept; its docstring explains the name. This closes
  the first item of `LEAN_COVERAGE.md` §3.6.
- `scripts/audit.sh`: the audit line is now counted before the summary copies it into the same log.
  The 2026-09-21 log therefore reported "passing #assert_standard_axioms lines: 2" for a single
  module-wide assertion; the new log reports 1. Exit conditions are unchanged.
- `README.md`, `LEAN_COVERAGE.md`, `CHANGES.md`: they name r6. `LEAN_COVERAGE.md` also no longer says
  that the article quotes no job count or describes a run of 18 September with SHA-256 hashes and a
  Python script (both were true of r5 only), gives `lake exe cache get` as the first reproduction
  step, and files `MinSpec.no_strict_retraction` as a result beyond `cor:section` (as `README.md`
  now does too). The labeled `LA ≠ L` gloss is made precise in the same way as in the header.
  `README.md` no longer links to the manuscript under the untracked `doc/` directory, and it has
  separate placeholders for the version DOI of the article revision and of this Lean package.

### Release build

`scripts/audit.sh` (exit 0) on 25 September 2026 at 11:36 UTC, environment pins unchanged. It was a
clean build of the project: the project's own `.lake/build` was moved aside first, so all 26 Lean
files were compiled in this run; mathlib came from the pinned prebuilt cache.

- `lake build` green, **2272 jobs**, no errors and no warnings;
- the source scan finds no forbidden construct in Lean code;
- all **2766 declarations in 25 modules** depend only on `propext`, `Classical.choice` and
  `Quot.sound`.

The figures are those of the 2026-09-21 run, as expected for comment-only changes. `BUILD_LOG.txt`
was regenerated for this run: new date, new blob hashes for the six changed files, r6 as reference
paper. The 2026-09-21 log is in git history at commit `826d0bd`. A second, fully cached run of
`scripts/audit.sh` also exits 0: Lake replays the stored messages of an up-to-date module
("Replayed ObserverEquivariance"), so the module-wide audit line appears even when nothing is
rebuilt.

When the final article revision exists, repeat this step: point the header of
`ObserverEquivariance.lean` and the three companion documents at it, rerun `scripts/audit.sh` and
regenerate `BUILD_LOG.txt`.
