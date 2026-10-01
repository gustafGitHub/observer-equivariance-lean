# observer-equivariance-lean

A Lean 4 + [mathlib](https://github.com/leanprover-community/mathlib4) formalization of the
normal-form, descent, calibration and lift-classification results (Sections 2–7) of

> G. Ullman, *Symmetry Between Perspectives: Invariant Calibration and Symmetry Lifts*,
> Zenodo version 14,
> DOI [`10.5281/zenodo.23040249`](https://doi.org/10.5281/zenodo.23040249).
> Concept DOI: [`10.5281/zenodo.17077437`](https://doi.org/10.5281/zenodo.17077437) (always
> resolves to the latest version).

Version DOI of this Lean package (release v2.0.0):
[`10.5281/zenodo.23079443`](https://doi.org/10.5281/zenodo.23079443).

All labels below (`def:data`, `thm:strict`, `cor:invariant-calibration`, …) are LaTeX labels of
the article. The paper's sections are `sec:data` (§2), `sec:normalform` (§3), `sec:descent` (§4,
containing `prop:comparisons`), `sec:symmetries` (§5, containing `sec:implementation` and
`ex:complex-obstruction`), `sec:law` (§6, containing `sec:records`) and `sec:boundaries` (§7,
containing `sec:holonomy`). Section 9 (`sec:lean`) describes this development, with the four
modules `Comparisons`, `Implementations`, `Examples/ComplexObstruction` and
`Examples/RecordsRecovery` in its subsection `sec:lean-modules`.

## Layout

The entry point is [`ObserverEquivariance.lean`](ObserverEquivariance.lean): it imports every
module and runs the module-wide axiom audit. Its header carries a module map and a directory
of the principal declarations per paper label.

| Module | Paper labels |
| --- | --- |
| `Core` | `def:data`, `lem:coordinates`, `prop:fullness`, `prop:cartesian`, `rem:groupoid`, `def:lifts`, `thm:strict`, `thm:twisted`, `def:law` |
| `ProductModel` | `thm:normalform` (product side); model for `ex:twist`, `sec:records` |
| `MinSpec`, `MinSpecCorrespondence` | `rem:audit` (both directions), `lem:coordinates` |
| `NormalForm` | `thm:normalform`, `cor:section`, `rem:groupoid` |
| `Descent` | `def:vertical-trivial`, `thm:descent`, `prop:weak-descent`, `ex:invariant` |
| `Residual`, `ResidualCategory` | `prop:residual` and the display after it |
| `Calibration` | `cor:invariant-calibration` |
| `Comparisons` | `prop:comparisons` |
| `Implementations` | `sec:implementation`, `prop:data-implementation`, `eq:implementation-intertwiner` |
| `LocalLifts` | `lem:local` |
| `Components` | `prop:components`, `prop:nocleavage` |
| `BaseChange`, `Cocycles`, `BaseChangeCocycle` | `prop:basechange`, `sec:normalization` |
| `Examples/Twist`, `Examples/TwoObject`, `Examples/NonFaithful`, `Examples/Holonomy` | `ex:twist`, the example after `prop:nocleavage`, `ex:nonfaithful`, `sec:holonomy` |
| `Examples/Records`, `Examples/RecordsCalibration` | `sec:records` |
| `Examples/ComplexObstruction` | `ex:complex-obstruction` |
| `Examples/RecordsRecovery` | the measurement calculations of `sec:records`, including the sign-orbit row of `tab:recovery-tasks` |
| `AxiomAudit` | the executable audit commands (no paper content) |

## What is formalized

### Normalized data and the minimal specification (`sec:data`)

`OEData G p` extends `NormalizedPreDatum G p` — clauses (N1)–(N5) of `def:data`, except that the
pre-datum carries the chosen vertical arrows only as arrows, not as isomorphisms, and keeps one
redundant field `act_free` (freeness, which `lem:coordinates` derives) — by the single field
`p_faithful`, which is (N6). Everything else the paper derives is derived here: fullness
of `p` is `OEData.isFull`, and invertibility of the chosen vertical arrows is
`OEData.ltrans_isIso`. The coordinate identities of `lem:coordinates` are `OEData.coord_act`,
`OEData.reind_eq`, `OEData.coord_reind` and `OEData.coordinate_identities`; freeness is proved
from the coordinates rather than read off a field.

`rem:audit` is formalized in both directions. `MinSpec G p` is the minimal specification (`p`
full and faithful, plus a based bijection `e : O ≃ S × G` with `(e x).1 = p.obj x`);
`OEData.toMinSpec` and `MinSpec.toOEData` are mutually inverse (`oeDataEquivMinSpec`), the
chosen transport and vertical arrows being the *unique* lifts with the prescribed endpoints.
`OEData.ext_of_coord` is the precise form of "(N3)–(N4) add no freely variable transport data".

### Normal form, section, cartesianness (`sec:normalform`)

- **Strict normal form (`thm:normalform`).** `normalFormTo` and `normalFormFrom` are strict
  inverse functors: `normalFormTo_comp_normalFormFrom : N ⋙ M = 𝟭 O` and
  `normalFormFrom_comp_normalFormTo : M ⋙ N = 𝟭 (S × Pair G)`, as equalities of functors, both
  lying over `S` on the nose (`normalFormTo_fst`, and `MinSpec.normalFormTo_comp_fst` for the
  minimal specification; `normalFormFrom_comp_fst`) and
  intertwining the right `G`-actions (`normalForm_equivariant`).
  `productNormalForm : O ≌ S × Pair G` and `projectionEquivalence` are the weak (equivalence)
  form.
- **Cartesianness (`prop:cartesian`).** `IsCartesianOver` is the strong existence-*and*-
  uniqueness property; `OEData.chi_isCartesian` and `OEData.isCartesian_of_fullyFaithful` show
  the chosen arrows — in fact all arrows — have it, and `OEData.chi_split_cartesian` bundles
  this with the splitting laws.
- **Section (`cor:section`).** `StrictSection p` carries a strict `B ⋙ p = 𝟭 S` together with a
  vertical natural isomorphism `η : p ⋙ B ≅ 𝟭 O`; `OEData.strictSection` builds it with
  `B.obj s = b_s`. Beyond what `cor:section` claims (the article asserts only that `p` is an
  equivalence), the projection is *not* a strict isomorphism: `MinSpec.no_strict_retraction` (for
  `[Nontrivial G] [Nonempty S]`).
- **Groupoid remark (`rem:groupoid`).** `OEData.base_hom_isIso` takes the groupoid property of
  `O` as an **explicit hypothesis** `hO : ∀ {x y : O} (f : x ⟶ y), IsIso f`; it is not a general
  theorem, and the development never assumes that base or total arrows are invertible. The
  converse direction is `OEData.hom_isIso_of_base_isIso`.

### Presentation independence, residual actions, calibration (`sec:descent`)

- **Strict factorization (`thm:descent`).** For an arbitrary target category `C`,
  `VerticallyTrivial p F ↔ ∃! E : S ⥤ C, p ⋙ E = F` (`strictSection_descent`, with
  `MinSpec.descent` and `OEData.descent`), plus the bundled factor form
  `strictSection_descent_factor` and the natural-transformation statements `natTrans_descent`
  and `natTrans_descent_of_eq`. Weak factorization is automatic for every `F`
  (`prop:weak-descent`: `weakDescentIso`, `weak_descent`).
- **Residual actions (`prop:residual`).** `OEData.IsInvariant d F` is strict invariance
  `R_h ⋙ F = F`. Invariant functors correspond to functors on `S × BG`
  (`invariant_iff_factors`, `productInvariant_iff_factors`), equivalently to `ResidualData`
  (`functorProdBGEquivResidualData`); the residual action itself is
  `residualAction d F hF s : G →* Aut (F.obj (d.base s))`, and strict descent holds exactly
  when it is trivial (`invariant_descends_iff_residual_trivial`). The category-level display is
  `InvFun d C ≅ Fun(S × BG, C) ≅ Fun(S, C^{BG})` (`invFunToProdBG`, `prodBGToInvFun`,
  `curry_comp_uncurry_prodBG`), and `exists_not_isInvariantNatTrans` shows `InvFun` is not a
  full subcategory.
- **Invariant calibration (`cor:invariant-calibration`).** The three conditions — an invariant
  natural isomorphism to shared data, strict factorization, triviality of every residual action
  — are equivalent: `calibration_i_iff_ii`, `calibration_ii_iff_iii`, `calibration_i_iff_iii`,
  bundled as `invariant_calibration_tfae` and `invariant_calibration_list_tfae`. Unrestricted
  calibration is always available (`unrestricted_calibration_exists`, with the explicit witness
  `unrestrictedCalibration`), and is invariant precisely in the trivial case
  (`unrestrictedCalibration_invariant_iff`).

### Classification of symmetry lifts (`sec:symmetries`)

Admissible lifts (`def:lifts`) are collected in the groups `AutBoxG d` (over all of
`StrictAut S`), `AutBoxGOver d H` (the paper's `Sym_H(p)` for a selected `H ≤ StrictAut S`) and
their twisted versions `AutBoxGθ d θ`, `AutBoxGθOver d H θ`.

- **Coordinate description (`lem:local`).** An equivariant functor over `A` has a unique
  multiplier `k = liftMultiplier d F` with `F(b_s · g) = b_{A s} · (k(s) g)` (`lift_obj_eq`,
  `multiplier_unique`), its arrow map is forced (`lift_map_eq_liftOver`), and in the normal
  form it *is* `(s, g) ↦ (A s, k(s) g)` (`normalForm_lift_eq`). Transport preservation is
  exactly constancy of `k` along arrows (`preservesCleavage_iff_multiplier`), every `k` gives a
  lift (`liftByMultiplier`), and every element of the lift group arises this way
  (`eq_autBoxGOfMultiplier`). None of this uses connectedness.
- **Connected-base classification (`thm:strict`).** `lift_exists` and `rigidity` give
  existence and uniqueness up to a normalized fiber translation; at group level `Φ` / `ΦOver`
  are surjective, `ΛHom` / `ΛHomOver` injective, and `ker_Φ_eq_range_Λ` /
  `ker_ΦOver_eq_range_ΛOver` identify the kernel, with the canonical section `liftHom` /
  `liftHomOver`. The packaged form is

  ```
  autBoxGOverMulEquivProd : AutBoxGOver d H ≃* G × H        -- needs [IsConnected S]
  autBoxGMulEquivProd     : AutBoxG d     ≃* G × StrictAut S
  ```

  Each `Λ d g` is naturally isomorphic to `𝟭 O` (`idIsoΛ`, `ΛIsoId`): a nontrivial element of
  the *strict* group can still be isomorphic to the identity — that is the difference between
  strict presentation data and autoequivalences modulo isomorphism, not a contradiction.
- **Twisted equivariance (`thm:twisted`).** For a twist `θ : H →* MulAut G` on the selected
  subgroup, `autBoxGθOverMulEquivSemidirect : AutBoxGθOver d H θ ≃* G ⋊[θ] H` (and
  `autBoxGθMulEquivSemidirect` for the full base group), with the conjugation law
  `liftHomθOver_conj`. Trivial twist returns the untwisted theorem
  (`autBoxGθOverOneMulEquiv`). `ex:twist` is realized concretely: base `Pair (Fin 2)`,
  `G = C₃`, `θ_A(g) = g⁻¹` with `twistθ_ne_one`, giving `twistSym` and `twistSymPerm` with
  `c3c2MulEquivS3 : C₃ ⋊ C₂ ≃* S₃`.
- **Dependence on normalization (`prop:basechange`, `sec:normalization`).** `OEData.rebase d c`
  moves the basepoints to `b_s · c`; on a connected base every parallel family is such a
  rebasing for a unique `c` (`parallel_family_eq_translate`, `exists_unique_eq_rebase`), and the
  comparison formulas are `coord_eq_of_base`, `Λ_eq_conj_of_base`, `liftFunctorθ_eq_conj_of_base`.
  The lift groups themselves do not move (`autBoxGCongr`, `autBoxGOverCongr`,
  `autBoxGθOverCongr` are the identity on `hom`). The cocycle reading is pure group theory in
  `OECocycle` (`coboundary`, `IsCocycle`, `H1`, `cocycleSectionEquiv`, `H1EquivSectionClasses`,
  `H1EquivComplementClasses`), and the bridge lemmas show the change of normalization is a
  coboundary whose class in `H¹(H, G)` is trivial (`baseChange_twistFactor_eq_coboundary`,
  `liftHomθOver_rebase_conj_ker`, `liftHomθOver_rebase_class`).
- **Disconnected bases (`prop:components`).** With **no** connectedness and **no** nonemptiness
  hypothesis,

  ```
  autBoxGOverMulEquivComponents :
    AutBoxGOver d H ≃* (ConnectedComponents S → G) ⋊[componentAction H G] H
  ```

  with the degenerate cases `componentFunctions_unique_of_isEmpty` (empty base) and
  `autBoxGOverMulEquivProdOfComponents` (connected base, recovering `G × H`), and the explicit
  swap example showing a disconnected base need not give a direct product.

### Law data and the measurement model (`sec:law`)

`strictLawStabilizer L` is the strict stabilizer `{A | A.hom ⋙ L = L}` of law data `L : S ⥤ C`,
and `lawPreservingAutBoxMulEquiv : LawPreservingAutBox d L ≃* G × strictLawStabilizer L` is the
law-preserving classification: not every strict automorphism of the base is a symmetry of the
law. The same theorem restricts to a state stabilizer (`stateStabilizer`,
`stateStabilizerAutBoxMulEquiv`); the action of `H_L` on states is a hypothesis, since the paper
specifies none.

`sec:records` is formalized as the finite algebraic model the paper defines: the connected base
`RecDom` of nonempty observation domains in `{0,1,2}` (`RecDom.isConnected`, with a
non-invertible arrow), the record spaces `recordSpace` cut out by the free-particle relation,
the law functor `L₀ τ`, the sign group `G = ℤˣ` with `recData = productData RecDom ℤˣ`, the
reflection symmetry `recA` and the selected subgroup `recH ≅ C₂`, and the lift group
`recSym : AutBoxGOver recData recH ≃* C₂ × C₂`. The covariant implementation is `recα` with its
involution coherence. On the calibration side, the raw-record functor `recD` is strictly
invariant (`recD_isInvariant`) with residual sign action (`recD_residualAction_hom`) and does
not factor strictly (`recD_not_factors`); the calibration `recC : 𝒟 ≅ L p` exists but depends on
the convention (`recC_hom_app_act`, `recC_not_invariant`), and no invariant calibration exists
(`recD_invariantNatTrans_eq_zero`, `recD_no_invariant_iso`, `recD_no_invariant_calibration`).
The paragraph "Information, compatibility, and exact recovery" is formalized by `recInfo_even`,
`recInfo_vertical_naturality_iff_even`, `recInfo_invariant_ne_id` and `recInfo_no_recovery`.

### Boundary calculations (`sec:boundaries`)

- **Dropping transport preservation (`prop:nocleavage`).** `AutEquivOver d H` collects the
  merely equivariant lifts; `autEquivOverMulEquiv : AutEquivOver d H ≃* (S → G) ⋊[objectAction H G] H`,
  with kernel `kerΦEquivOverMulEquiv : … ≃* (S → G)` and the embedding
  `autBoxGOverToAutEquivOver` characterized by `autEquivOver_preservesCleavage_iff`. The
  two-object example makes the restriction visible: the unrestricted kernel is `C₂ × C₂`
  (`kerEquivProd`), the transport-preserving one is the diagonal `C₂`
  (`transportKerMulEquiv`), and `flipOne_not_preservesCleavage` / `diagSubgroup_ne_top` show the
  inclusion is proper.
- **Dropping faithfulness (`ex:nonfaithful`).** `nonfaithfulPreDatum K` satisfies (N1)–(N5) but
  not (N6) (`nonfaithfulProj_not_faithful`), so it is no `OEData` for any presentation group
  (`nonfaithful_isEmpty_OEData`); its lift kernel is `MulAut K` (`nonfaithfulLiftKernelEquiv`),
  which for `K = C₃` is nontrivial although `G` is trivial
  (`nonfaithful_kernel_not_presentationGroup`).
- **Holonomy (`sec:holonomy`, `prop:holonomy`).** The ρ-twisted model `HolTotal` satisfies
  (N4) exactly when `ρ = 1` (`holReind_holBase_iff`, `holonomy_not_OEData`), and its lift group
  sits in the extension `holLift_exact` with kernel the centralizer of `im ρ`
  (`holLiftProjKerEquiv`). Both special cases are formalized: the `S₃` transposition
  (`holS3CentralizerEquiv`) and the nonsplit `Q₈` extension (`holQ8_no_section`).

### Comparisons, implementations and further examples (`sec:lean-modules`)

The general statements of these four modules are proved in the strict product normal form
`S × Pair G`, for arbitrary base and target categories — the setting in which the paper states
them — and are not separately restated for an abstract `OEData`; the passage is the normal-form
and residual-data machinery above.

- **Comparisons and prescribed targets (`prop:comparisons`, module `Comparisons`).** For
  residual data `D`, `ResidualData.presentationFunctor D` is the composite
  `residualQ S G ⋙ D.toFunctor` of `prop:residual` — not new data — and it is strictly invariant
  (`presentationFunctor_isInvariant`). Unrestricted natural transformations between two such
  functors correspond bijectively to natural transformations of the base data:
  `comparisonEquiv : (D.presentationFunctor ⟶ D'.presentationFunctor) ≃ (D.E ⟶ D'.E)`, built
  from `comparison` / `restrictComparison` with both round trips
  (`restrictComparison_comparison`, `comparison_restrictComparison`) and the component formula
  `comparison_app : α_(s,⟨a⟩) = (σ_s a).inv ≫ β_s ≫ (σ'_s a).hom` (`comparison_app_residual`
  is the paper's `σ_s(a⁻¹)` form). A comparison is invertible exactly when its restriction is
  (`isIso_comparison_iff`), invariant exactly when it is independent of the presentation
  coordinate (`invariant_iff_constant`), and that holds exactly under the intertwining relation
  `comparison_invariant_iff`. For a prescribed target `L : S ⥤ C` (carried by
  `ResidualData.trivial L`, whose presentation functor is `Prod.fst S (Pair G) ⋙ L`, the
  product-coordinate form of `L p`, by `trivial_presentationFunctor`), an
  unrestricted isomorphism exists iff `D.E ≅ L` (`prescribed_iso_iff`), and an *invariant* one
  iff in addition every `σ_s` is trivial (`prescribed_invariant_iso_iff`).
- **Invariant implementations (`sec:implementation`, `prop:data-implementation`, module
  `Implementations`).** `ResidualData.twisted D A θ` is the pullback datum `A ⋙ D.E` with
  `r ↦ σ_{A s}(θ r)`; it computes the residual data of the canonical twisted lift, on objects
  *and* arrows (`twisted_presentationFunctor`, `canonical_product_lift_eq`,
  `liftFunctorθ_comp_presentationFunctor` — the lift is the canonical lift `liftFunctorθ` of
  `thm:twisted`). The criterion is the bijection

  ```
  implementationEquiv : D.InvariantImplementation A θ ≃ D.TwistedIntertwiner A θ
  ```

  where `TwistedIntertwiner` is `β : A ⋙ D.E ≅ D.E` satisfying
  `eq:implementation-intertwiner`, with the existence form `invariant_implementation_iff` and
  the component formula `implementation_app` (`α_(s,⟨a⟩) = β_s`, independent of `a`). It is a
  criterion for **one**
  selected base transformation: no coherence for a family indexed by a group is asserted or
  proved. For an abelian presentation group, constant fibre translations leave the residual data
  unchanged (`translated_twisted_presentationFunctor`,
  `translated_lift_comp_presentationFunctor`, with `multiplier_product_lift_eq`).
- **A lift with no invariant complex-linear implementation (`ex:complex-obstruction`, module
  `Examples/ComplexObstruction`).** On the `ex:twist` datum (`S = Pair (Fin 2)`, `G = C₃`,
  interchange `swapFunctor`, twist `r ↦ r⁻¹`) the character is the actual primitive root
  `omega = exp(2πi/3)` (`omega_primitive`, `omegaUnit`, `character`, `character_generator`),
  acting on `ModuleCat ℂ` by scalars (`representation`, `complexData`, `F_isInvariant`). Every
  complex-linear intertwiner between the inverse and the original character vanishes
  (`intertwiner_eq_zero`, no invertibility assumed), so there is no invariant complex-linear
  implementation — `no_invariant_complex_implementation`, and
  `no_invariant_complex_implementation_any_lift` for **every** transport-preserving lift over the
  interchange that is twisted-equivariant for the inversion twist, via the twisted classification
  `exists_unique_eq_liftFunctorθ_comp_Λ`. The unrestricted comparison does exist
  (`unrestrictedImplementation`, whose component at `(s, ⟨g⟩)` is multiplication by
  `(character g)²`, `unrestrictedImplementation_app`)
  and is not invariant (`unrestrictedImplementation_not_invariant`). After restriction of
  scalars to `ℝ` (`realification`, `realData`, `realData_presentationFunctor`) complex
  conjugation is an allowed morphism: `realImplementation` is an invariant implementation
  (`real_intertwines`, `realImplementation_app`) and satisfies the involution equation
  (`realImplementation_involution`). The target category, not the lift, decides.
- **Measurement calculations (`sec:records`, `tab:recovery-tasks`, module
  `Examples/RecordsRecovery`).** A `Procedure` is a family of maps of record spaces with no
  presentation-coordinate argument; `IsEven` and `RespectsRestrictions` are the two conditions,
  stated separately because neither is automatic. The identity procedure is not even
  (`identity_not_even`); the even procedure `max |y_j| · 1` is even (`maxProcedure_even`) but
  does not commute with restriction (`maxProcedure_not_natural`, for `τ ≠ 0`). The third row of
  `tab:recovery-tasks` is realized in `Type` (the paper's `Set`): the sign-orbit functor
  `orbitFunctor` with the recovery map `orbitRecovery`, which
  is natural under restrictions (the naturality field of `orbitRecovery`), invariant
  (`orbitRecovery_invariant`) and exact on signs, `K_I (ε y) = [y]` (`orbitClass_sign`).
  The orbit set is **not** the linear coinvariant quotient: in `ℝ`-modules those relations
  generate everything, so the quotient vanishes (`signRelations_eq_top`,
  `linear_coinvariants_zero`, `linear_coinvariants_subsingleton`). A nonzero reference
  observation recovers the sign and the value as scalar identities in `ℝ`
  (`reference_determines_sign`, `reference_recovers_value`); these are not lifted to the record
  functors, so they add no natural transformation to the ones ruled out above. Finally the time reflection on `(q, v)` is an involution whose
  fixed trajectories are exactly those with `v = 0` (`reflectTrajectory_involution`,
  `reflectTrajectory_fixed_iff`), and `recα_trajectory` identifies this parameter calculation
  with the record-space transformation `recα`.

## Assumptions and modelling choices

The general development assumes only
`{S O G : Type*} [Category S] [Category O] [Group G] {p : O ⥤ S}`. **Neither category is a
groupoid**; the only `Groupoid` instances in the project are those of the concrete categories
`Pair X` and `Lab B Q`. Target categories are arbitrary.

- **`p_faithful` (N6)** is the only extra field beyond `NormalizedPreDatum`: the fibration is
  thin. Fullness is *derived* (`OEData.isFull`), and so is invertibility of the vertical arrows
  (`OEData.ltrans_isIso`).
- **`[IsConnected S]`** appears only where the paper uses connectedness: `rigidity`,
  `rigidityθ`, `unbundled_lift_classification`, the kernel identities, the four classification
  isomorphisms (`autBoxGMulEquivProd`, `autBoxGOverMulEquivProd`, `autBoxGθMulEquivSemidirect`,
  `autBoxGθOverMulEquivSemidirect`), their law and state specializations, the `existsUnique_Λ…`
  lemmas, the connected-base lemmas of `LocalLifts`, the connected specializations
  `componentFunctionsMulEquiv`, `autBoxGOverMulEquivProdOfComponents` and `componentsUnique` of
  `Components`, the parallel-family statements of `BaseChange` and all of `BaseChangeCocycle`;
  the header of `ObserverEquivariance.lean` gives the complete list. The normal form, the
  section, descent, residual actions and calibration carry no such hypothesis, and neither does
  the componentwise classification itself.
- **`[Nonempty S]`** suffices for `ΛHom_injective`, `ΛHomOver_injective`, `ΛHomθ_injective`,
  `ΛHomθOver_injective` (injectivity fails over an empty base) and for
  `parallel_basepoints_const_unique`; `MinSpec.no_strict_retraction` also needs
  `[Nontrivial G]`.
- **Admissibility** is `IsGEquivariant` (object level) together with `PreservesCleavage`. The
  morphism-level conditions are *derived* from faithfulness, and the derivation is itself
  formalized (`isGEquivariant_map_actHom`, `PreservesCleavage.map_chi`, `OEData.base_unique`,
  `AutBoxG.ext_hom`).
- **Strict groups.** `Aut(S)` and the lift groups are groups of strict automorphisms
  (`StrictAut S`), as in the paper: an equivalence has no strict inverse, and `Λ_g ≅ 𝟭` would
  collapse the kernel. They multiply in operator order, `(e₁ * e₂).hom = e₂.hom ⋙ e₁.hom`, while
  Lean composes diagrammatically.
- **`Λ d g`** acts on arrows by transport along the chosen vertical arrows `ltrans`, not along
  the cleavage `χ`.
- **Naming.** `OEData.IsInvariant` is namespaced because mathlib has a root `IsInvariant`.
  The aliases `strict_lift`, `strict_liftθ` and `exact_sequence` name `lift_exists`,
  `twisted_lift_exists` and `unbundled_lift_classification`. `CHANGES.md` records the naming and
  encoding decisions.

## The representation question in `sec:records`

The paper's `LA ≠ L` is proved twice. For the **unlabeled** law functor `L₀ τ` the inequality
`recA_comp_L₀_ne` holds for every `τ ≠ 0`; it is proved by evaluating a concrete record through
the linear casts of `ModuleCat ℝ`, not by a failure of `rfl` or by deciding an equality of
carrier types. This is the informative statement, and it gives
`recA_not_mem_strictLawStabilizer_L₀`. The **labeled** reading keeps the observation domain as
object data, with target `Pair RecDom × ModuleCat ℝ` and law `Lℓ τ`; there `recA_comp_Lℓ_ne`
follows from the labels alone, and the labels together with the thinness of the base force the
strict stabilizer to be trivial (`strictLawStabilizer_Lℓ_eq_bot`, proved for `Lℓ τ`; the same
argument would apply to any labeled functor of this form), so that version carries no information
about the free-particle law.

## Not formalized

- The interpretive discussion (`sec:introduction`, `sec:scope`, `sec:related`).
- The cited background: smooth gauge theory and principal bundles, algebraic quantum field
  theory, Zeeman- and Wigner-type theorems, Noether's theorem. Nothing here yields conservation
  laws, infinitesimal generators or smooth actions, and no Lorentz group occurs anywhere.
- The remark after `cor:invariant-calibration` that the diagonal orbit category is
  `O/G ≅ S × BG` in the chosen coordinates: no orbit-category construction is made. The closest
  formal statement is the unique factorization `invariant_iff_factors` through `N ⋙ Q`.
- A general theory of coherent covariant implementations `α_A : L A ⇒ R_A L`: `sec:implementation`
  and `prop:data-implementation` are formalized for **one** selected base transformation, and
  nothing here supplies coherence for a family indexed by a group. The two concrete involution
  coherences are proved (`realImplementation_involution`, and `recα` in the record model).
- The measurement calculations do not package every absolute-value statistic as a natural
  transformation; `maxProcedure` is the one specified counterexample.

## Audit and reproduction

The audit is executable and part of the build: `ObserverEquivariance.lean` ends with
`#assert_standard_axioms_in_modules ObserverEquivariance`, defined in
`ObserverEquivariance/AxiomAudit.lean`. Unlike `#print axioms`, it **fails the build** if any
declaration of any imported `ObserverEquivariance.*` module — auxiliary `_proof_n` / `match_n`
constants included — depends on an axiom other than `propext`, `Classical.choice`,
`Quot.sound`.

In the pinned environment, the run of 2026-09-29 recorded in `BUILD_LOG.txt` reported:

- `lake build` green: 2272 jobs, no errors, no warnings;
- all **2766 declarations in 25 modules** depend only on the three standard axioms;
- no `sorry`, `admit`, project-specific `axiom` or `native_decide` in Lean code.

Every module imports the specific mathlib files it uses, not all of `Mathlib`. The declaration
count depends on that import surface: it counts the auxiliary `_proof_n` / `match_n` constants of
the imported `ObserverEquivariance.*` modules, so it is not a count of theorems, and counts are
comparable only between runs of the same import configuration.

Reproduce it with [`scripts/audit.sh`](scripts/audit.sh) (default log `BUILD_LOG_RAW.txt`),
which records the environment, runs `lake build`, scans all Lean code for forbidden constructs
with comments stripped, checks that the module-wide audit ran, and exits non-zero on any
failure.

The `#print axioms` block just above the audit command prints the axioms of selected
declarations as a diagnostic; the executable audit below it is the authoritative check.
[`BUILD_LOG.txt`](BUILD_LOG.txt) is the log of the recorded run: environment, exact commands, the
git blob SHA-1 and line count of every source file as built, the scan, the build, the audit line
for all 2766 declarations and the 18 `#print axioms` diagnostics.

Two companion documents: [`LEAN_COVERAGE.md`](LEAN_COVERAGE.md) maps each result of Sections
2–7 onto its Lean declarations, with the actual hypotheses and a status per row;
[`CHANGES.md`](CHANGES.md) records the naming and encoding decisions.

## Building

- Toolchain: `leanprover/lean4:v4.31.0-rc1` (pinned in `lean-toolchain`; install via
  [elan](https://github.com/leanprover/elan)).
- mathlib is pinned in `lake-manifest.json` (rev `8834d3761934044a64c98afb757c1673fad03521`).

```sh
lake exe cache get   # download the pinned mathlib .olean cache
lake build           # compiles every module and runs the axiom audit
scripts/audit.sh     # build + forbidden-construct scan + audit, into BUILD_LOG_RAW.txt
```

> Note: a fresh clone has no `.lake/` directory (it is gitignored). `lake exe cache get`
> fetches the pinned mathlib build (from the mathlib cache server, or reusing a local
> `~/.cache/mathlib` if present); `lake build` then compiles the modules of this project.
