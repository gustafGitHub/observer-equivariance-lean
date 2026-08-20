# observer-equivariance-lean

A Lean 4 + [mathlib](https://github.com/leanprover-community/mathlib4) formalization of the
product normal form and the lift-classification theorems (Sections 3–6) of

> G. Ullman, *Symmetry Between Perspectives: The Structure of Shared Reality — A Lean-Verified
> Normal Form for Observer-Dependent Presentations*.
> Zenodo — concept DOI: `10.5281/zenodo.17077437` (always resolves to the latest version).

Everything lives in a single file: [`ObserverEquivariance.lean`](ObserverEquivariance.lean).

## What is formalized

For a *normalized split torsor-groupoid datum* `p : O ⥤ S` — a projection separating a groupoid
`O` of concrete presentations from a category `S` of shared structural content, with a free
transitive right `G`-action on the object fibers, a chosen split cleavage, transport-compatible
basepoints, fiber coordinates and vertical translations, bundled as the structure `OEData`
(paper `def:oedata`) — the file proves:

### Derived fibration structure and the product normal form (paper §3)

- **`OEData.isFull`:** fullness of `p` is *derived*, not assumed.
- **`IsCartesianOver` / `OEData.chi_isCartesian` (`prop:cartesian`):** the chosen cleavage arrows
  are **strongly** cartesian — the full existence-*and*-uniqueness universal property, not a weak
  lifting condition. (`OEData.isCartesian_of_fullyFaithful`: in fact *every* arrow of `O` is.)
- **`productNormalForm` (`thm:productnormalform`):** the normalized data trivialize the
  presentation on the nose,

  ```
  productNormalForm d : O ≌ S × Pair G
  ```

  where `Pair G` is the pair (codiscrete) groupoid on `G`, the paper's `Pair(G)`. The comparison
  functor is `normalFormTo` (`productNormalForm_functor`), and its compatibilities are named:
  `normalFormTo_fst` (first projection is `p`, by `rfl`), `normalForm_equivariant` (functorial
  `G`-equivariance), `normalForm_base` (`b_s ↦ (s,1)`), `normalForm_reind` (reindexing preserves
  the coordinate).
- **`projectionEquivalence`:** since `Pair G` is categorically contractible, `p` itself is an
  equivalence `O ≌ S` (`projectionEquivalence_functor : … = p`).
- **`OEData.base_hom_isIso` (`cor:basegroupoid`):** every base morphism is invertible.

### Strict classification of symmetry lifts (paper §4)

Write `Sym_H(p)` for the paper's admissible symmetry group (`def:autbox`); the Lean names are
`AutBoxG d` for the ambient group and `AutBoxGOver d H` for its restriction to a selected
subgroup `H ≤ Aut(S)`.

- **`lift_exists` (`lem:canonical-lift`):** every base autoequivalence admits a `G`-equivariant,
  cleavage-preserving lift. This is the ∃-witness of the predicates; the *bundled* canonical lift
  is `liftAut`, and the canonical section homomorphism is `liftHom`.
- **`rigidity` (`lem:rigidity`):** two such lifts of one base symmetry differ by a **unique**
  normalized fiber translation `Λ d g` (`∃! g`).
- **`unbundled_lift_classification`:** the elementary `∀/∃/↔` form of the classification.
- **Group form (`thm:strict-classification`):** `Φ : AutBoxG d →* StrictAut S` and
  `ΛHom : G →* AutBoxG d` are genuine `MonoidHom`s with `Φ_surjective`, `ΛHom_injective` and
  `ker_Φ_eq_range_Λ`, i.e. the split short exact sequence
  `1 → G → Aut□_G(O/p) → Aut(S) → 1`, packaged as the explicit **direct product**

  ```
  autBoxGMulEquivProd : AutBoxG d ≃* G × StrictAut S      -- needs [IsConnected S]
  ```

  Only the *canonical normalized* section centralizes the kernel (`ΛHom_comm_liftHom`); an
  arbitrary lift may carry a left translation and then conjugate `Λ` nontrivially.
- **`idIsoΛ`:** each `Λ d g` is naturally isomorphic to `𝟭 O`. It is a nontrivial element of the
  *strict* presentation group nonetheless — that is the difference between strict presentation
  data and autoequivalences modulo natural isomorphism, not a contradiction.

### Restriction to a selected subgroup, and to a law (paper §4, §6)

The paper states its classification for an arbitrary selected `H ≤ Aut(S)`, and this is formalized
directly:

- **`autBoxGOverMulEquivProd : AutBoxGOver d H ≃* G × H`** where `AutBoxGOver d H = Φ⁻¹(H)`, with
  the full package `ΦOver` / `ΛHomOver` / `liftHomOver`, `ΦOver_surjective`,
  `ΛHomOver_injective`, `ker_ΦOver_eq_range_ΛOver`.
- **`strictLawStabilizer L`** (`def:law-symmetry`): the *strict* stabilizer `{A | A.hom ⋙ L = L}`
  of law data `L : S ⥤ C`, and the law-preserving specialization (`cor:law`)

  ```
  lawPreservingAutBoxMulEquiv : LawPreservingAutBox d L ≃* G × strictLawStabilizer L
  ```

  This is the formal counterpart of the paper's physically relevant statement: not every strict
  category automorphism is a physical symmetry — only the law-preserving ones.

### θ-equivariance and semidirect symmetry (paper §5)

For a twist `θ` (base symmetries acting on the structure group), `θ`-twisted equivariance
`F(x·g) = F x·(θ_A g)` gives the twisted sequence and the conjugation law
`liftHomθ_conj : Ã ∘ Λ_g ∘ Ã⁻¹ = Λ_{θ_A g}` (`twisted_lift_exists`, `rigidityθ`,
`Φθ_surjective`, `ΛHomθ_injective`, `ker_Φθ_eq_range_Λθ`), packaged as explicit **semidirect
products** in both the ambient and the subgroup form:

```
autBoxGθMulEquivSemidirect     : AutBoxGθ d θ       ≃* G ⋊[θ] StrictAut S
autBoxGθOverMulEquivSemidirect : AutBoxGθOver d H θ ≃* G ⋊[θ] H
```

The subgroup version takes `θ : H →* MulAut G`, i.e. a twist defined **only on the selected
subgroup** — the shape the paper's Poincaré template needs. Setting `θ = 1` recovers the direct
product. The twisted law-preserving analogue is obtained by instantiating the subgroup theorem at
`H := strictLawStabilizer L`; it is not separately named.

### Witnesses (paper §7)

- **`witness` / `witness₂`:** a concrete `OEData` for an arbitrary group `G`, and an explicit
  `|G| = 2` instance, so the theorems are non-vacuous and `p_faithful` is consistent with a
  nontrivial structure group.
- **`labData K Q`:** the `Q`-labelled groupoid with object set `K` over `SingleObj Q`, carrying a
  nontrivial functorial twist `θSingleObj K`, packaged as a genuine group isomorphism
  `θSingleObjEquiv : StrictAut (SingleObj G) ≃* MulAut G`.
- **A fully closed nontrivial twist:** for `G3 = Multiplicative (ZMod 3)`, inversion is a
  nontrivial automorphism (`zmod3NegMulAut_ne_one`), hence `θSingleObj_zmod3_ne_one`, and
  `zmod3SemidirectWitness` realizes the corresponding `≃* SemidirectProduct` with `θ ≠ 1`.

These witnesses have **one-object bases**; `rigidity` uses the full connectedness hypothesis and
so applies to bases with arbitrarily many objects. The arbitrary-base product model of
`ex:product` is immediate from the data but is not separately packaged as a declaration.

## Not formalized

The **literal** physical specializations are out of scope: Wigner–Uhlhorn, a literal
`ℝ⁴ ⋊ O(1,3)` frame bundle, the qubit phase model, and the interpretive discussion. The paper
presents Poincaré as an *algebraic semidirect template* (`ex:poincare`) for the shape proved
here; a literal Lorentz bundle additionally needs `O(1,3)`, which mathlib does not yet provide.
Nothing here yields Noether-type conservation laws (`rem:noether`): the normalized datum contains
no action functional, smooth one-parameter groups, or equations of motion.

## Assumptions

Beyond the data and axioms of `OEData` (paper `def:oedata` (N1)–(N6)), the results use exactly
two extra hypotheses:

- **`p_faithful : p.Faithful`** — the fibration is *thin*: at most one morphism between two
  objects over each base morphism (a torsor-groupoid fibration). This is the precise content of
  the "non-discrete" model. `p.Full` is **not** assumed — it is derived (`OEData.isFull`).
- **`[IsConnected S]`** — `S` is connected. Used in `rigidity`, the classification theorems and
  the kernel identities: connectedness makes the relative translation between two lifts globally
  constant. (`ΛHom_injective` and `ΛHomθ_injective` need only `[Nonempty S]`; injectivity is
  false over an empty base.)

Modelling choices worth flagging:

- `Λ_g` acts on in-fiber morphisms via a chosen vertical translation iso `ltrans`, not via the
  cleavage `χ`. A cleavage-only definition is type-correct only for *discrete* fibers, and
  discrete fibers together with the flat basepoint section and connected `O` would force `G`
  trivial.
- `Sym_H(p)` is captured by `IsGEquivariant` (object-level `G`-equivariance) together with
  `PreservesCleavage`. The morphism-level conditions are **derived** from `p_faithful`, and this
  derivation is itself formalized: `isGEquivariant_map_actHom` and `PreservesCleavage.map_chi`.
  Base-symmetry uniqueness is `OEData.base_unique`, giving `AutBoxG.ext_hom`.
- `Aut(S)` and `Aut□_G(O/p)` are the groups of **strict** (on-the-nose) automorphisms
  (`StrictAut S` / `AutBoxG d`), matching the paper's convention. Equivalences (`≌`) cannot form
  the group: they have no strict inverse, and `Λ_g ≅ 𝟭` would collapse the kernel.

Earlier names are retained as compatibility aliases: `strict_lift` → `lift_exists`,
`strict_liftθ` → `twisted_lift_exists`, `exact_sequence` → `unbundled_lift_classification`.

## Sorry-free

The build is clean (no `sorry`, `admit`, project-specific `axiom`, or `unsafe`). The file ends
with an executable `#print axioms` block auditing the principal theorem-level declarations; in
the pinned environment it reports:

```
'OEData.chi_isCartesian'          depends on axioms: [propext, Classical.choice, Quot.sound]
'productNormalForm'               depends on axioms: [propext, Classical.choice, Quot.sound]
'normalForm_equivariant'          depends on axioms: [propext, Classical.choice, Quot.sound]
'normalForm_base'                 depends on axioms: [propext]
'normalForm_reind'                depends on axioms: [propext]
'projectionEquivalence'           depends on axioms: [propext, Classical.choice, Quot.sound]
'OEData.base_hom_isIso'           depends on axioms: [propext, Classical.choice, Quot.sound]
'idIsoΛ'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'liftAut'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'autBoxGMulEquivProd'             depends on axioms: [propext, Classical.choice, Quot.sound]
'autBoxGOverMulEquivProd'         depends on axioms: [propext, Classical.choice, Quot.sound]
'lawPreservingAutBoxMulEquiv'     depends on axioms: [propext, Classical.choice, Quot.sound]
'autBoxGθOverMulEquivSemidirect'  depends on axioms: [propext, Classical.choice, Quot.sound]
'θSingleObj_zmod3_ne_one'         depends on axioms: [propext, Classical.choice, Quot.sound]
'zmod3SemidirectWitness'          depends on axioms: [propext, Classical.choice, Quot.sound]
'twisted_lift_exists'             depends on axioms: [propext, Classical.choice, Quot.sound]
'rigidityθ'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'normalFormTo_fst'                depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice` and `Quot.sound` are mathlib's three standard axioms; there is no
`sorryAx`. These are diagnostic commands: a successful build alone does not assert that the
output has a predetermined value, so the claim refers to the inspected output in the pinned
environment.

## Building

- Toolchain: `leanprover/lean4:v4.31.0-rc1` (pinned in `lean-toolchain`; install via
  [elan](https://github.com/leanprover/elan)).
- mathlib is pinned in `lake-manifest.json` (rev `8834d3761934044a64c98afb757c1673fad03521`).

```sh
lake exe cache get   # download the pinned mathlib .olean cache
lake build           # compiles ObserverEquivariance.lean (~1 min once mathlib is cached)
```

> Note: a fresh clone has no `.lake/` directory (it is gitignored). `lake exe cache get`
> fetches the pinned mathlib build (downloading from the mathlib cache server, or reusing a
> local `~/.cache/mathlib` if present); then `lake build` compiles this file in ~1 min.
> Verified from a clean checkout.
