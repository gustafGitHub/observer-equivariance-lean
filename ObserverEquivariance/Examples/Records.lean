import ObserverEquivariance.ProductModel

/-!
# Free-particle records and sensor polarity, first half (paper `sec:records`)

Paper labels covered (all in `sec:records`, plus `def:law` and `thm:strict` as used there):
* paragraph "The base and its law data": the base `S` of nonempty observation domains
  `I ⊆ T = {0,1,2}` with one arrow `u_{IJ} : I ⟶ J` iff `J ⊆ I` (`RecDom`), its connectedness
  (`RecDom.isConnected`), a non-invertible arrow (`RecDom.not_isIso_fromFull_single`), the record
  spaces `L(I)` (`recordSpace`), the restrictions `r_{IJ}` (`recRestrict`), the law functor
  `L = L₀ τ`, the description `L(T) = {q₂ - 2q₁ + q₀ = 0}` (`mem_recordSpace_full_iff`, uses
  `0 < τ`), and nontriviality of every `L(I)` (`recordSpace_nontrivial`, `L₀_exists_ne_zero`);
* paragraph "Presentations and their comparisons": `O = S × Pair(G)`, `p = Prod.fst`, with the
  signs represented exactly as `G = ℤˣ` (acting on real vector spaces by `((ε : ℤ) : ℝ) • ·`,
  lemmas `recSign_*`), and the normalized datum `recData := productData RecDom ℤˣ`
  (`recData_act`, `recData_base`, `recData_reind`);
* paragraph "A base symmetry and its implementation": `ρ(j) = 2 - j` (`recρ = Fin.rev`), the strict
  base involution `A(I) = ρ(I)` (`recA`), the selected subgroup `H = {1, A} ≅ C₂` (`recH`,
  `recHMulEquiv`, `recH_card`), the canonical lift `Ã(I,ε) = (ρ(I),ε)` (`recLift_obj`) commuting
  with the polarity change, the selected lift group `Sym_H(p) ≅ C₂ × C₂` (`recSym`), the natural
  linear isomorphism `α : L A ≅ L`, `(α_I x)_j = x_{ρ(j)}` (`recα`) with its involution coherence
  `α_I α_{ρ(I)} = id` (`recα_involution`, `recα_involution_natTrans`, and for labeled spaces
  `recαℓ_involution`), and the strict inequality `L A ≠ L`, both for the unlabeled law
  (`recA_comp_L₀_ne`, uses `τ ≠ 0`) and for explicitly labeled spaces (`recA_comp_Lℓ_ne`), so that
  `H` is not the strict stabilizer (`recA_not_mem_strictLawStabilizer_L₀`,
  `recH_not_le_strictLawStabilizer_L₀`, `recA_not_mem_strictLawStabilizer`).

## Representation of labeled observation spaces

The paper's claim `LA ≠ L` is made "for these explicitly labeled vector spaces". It is formalized
at two levels. Neither argument rests on a failure of `rfl`, or on deciding an equality of carrier
types (such as the carriers of `L(ρ{0})` and `L({0})`, which Lean can neither prove nor refute to
be equal).

**Unlabeled law.** For `L₀ τ : S ⥤ ModuleCat ℝ` (the paper's `L`: `I ↦ L(I) ⊆ ℝ^I`, restrictions
`r_{IJ}`) the inequality `recA.hom ⋙ L₀ τ ≠ L₀ τ` is proved for every `τ ≠ 0`
(`recA_comp_L₀_ne`). An equality of functors yields, via `Functor.congr_hom` on `u : T ⟶ {0}`,
`r_{ρ(T)ρ({0})} = c₁ ≫ r_{T{0}} ≫ c₂` with casts `cᵢ = eqToHom _` between objects of
`ModuleCat ℝ`. These casts are morphisms of `ModuleCat ℝ`, hence linear, and `c₁` is the cast
along `ρ(T) = T`, which acts as the identity on entries. Evaluating on the record `x_j = j` (take
`q₀ = 0`, `v = 1/τ`) gives `2` at index `2 ∈ ρ({0}) = {2}` on the left. On the right, `r_{T{0}}`
returns the entry `x_0 = 0`, so the result is `c₂(0) = 0`. Hence `2 = 0`, a contradiction. This is
the substantive statement about the law: `A ∉ H_L` for `L = L₀ τ`
(`recA_not_mem_strictLawStabilizer_L₀`).

**Labeled law.** For the literal reading "explicitly labeled vector spaces", the observation domain
is also kept as explicit object data. The target is the category `Pair S × ModuleCat ℝ`. Its
objects are pairs (label `⟨I⟩ : Pair S`, real vector space), and its morphisms
`(⟨I⟩, V) ⟶ (⟨J⟩, W)` are exactly the linear maps `V → W` (the `Pair` factor has a unique arrow
between any two labels, so it adds no morphism data). The forgetful functor to real vector spaces
is `Prod.snd`. The labeled law is `Lℓ τ = recLabel.prod' (L₀ τ)`, `I ↦ (⟨I⟩, L(I))`, with
`Lℓ τ ⋙ Prod.snd = L₀ τ` (`Lℓ_comp_snd`, by `rfl`). Here `LA ≠ L` follows from the labels alone:
the label of `(Lℓ τ)(A{0})` is `⟨{2}⟩` and that of `(Lℓ τ){0}` is `⟨{0}⟩` (`recA_comp_Lℓ_ne`).
The argument never looks at the record spaces. The strict stabilizer of `Lℓ τ` is trivial
(`strictLawStabilizer_Lℓ_eq_bot`). Its proof uses only the labels and the thinness of the base, so
it applies verbatim to *any* functor `I ↦ (⟨I⟩, V(I))`, whatever the law (this general form is not
stated as a separate declaration). So
`recA_not_mem_strictLawStabilizer` (for `Lℓ τ`) carries no information about the free-particle law.
The informative statement is the unlabeled one above.

The covariant implementation exists at both levels: `recα : recA.hom ⋙ L₀ τ ≅ L₀ τ` and
`recαℓ : recA.hom ⋙ Lℓ τ ≅ Lℓ τ`. The record component of `recαℓ` is `recα`
(`recαℓ_hom_app_snd`), and both satisfy the involution coherence (`recα_involution`,
`recαℓ_involution`).

## Conventions
* An arrow `I ⟶ J` of `RecDom` is a proof of `J.dom ⊆ I.dom` (wrapped in `PLift`); `RecDom` is
  deliberately a structure (not a subtype of `Finset`) so that mathlib's preorder category on
  `Finset` (with the opposite orientation) is not picked up.
* Elements of `(L₀ τ).obj I` are elements of the submodule `recordSpace τ I`; their entries are
  read with `Subtype.val x j` (`↑x j`).
* Operator order in the paper: `α_I α_{ρ(I)}` is `α_{ρ(I)} ≫ α_I` in Lean.
-/

open CategoryTheory

/-! ## The base `S` of observation domains -/

/-- An object of the base `S` of paper `sec:records` ("The base and its law data"): a nonempty
    subset `I ⊆ T = {0,1,2}` of observation times, encoded as a nonempty `Finset (Fin 3)`. -/
@[ext]
structure RecDom where
  /-- The set `I ⊆ T` of observation indices. -/
  dom : Finset (Fin 3)
  /-- Observation domains are nonempty. -/
  nonempty : dom.Nonempty

namespace RecDom

/-- The base category of paper `sec:records`: exactly one arrow `u_{IJ} : I ⟶ J` when `J ⊆ I`
    (restriction of a record to fewer times), none otherwise. -/
instance : SmallCategory RecDom where
  Hom I J := PLift (J.dom ⊆ I.dom)
  id _ := ⟨Finset.Subset.refl _⟩
  comp f g := ⟨g.down.trans f.down⟩

/-- The base of paper `sec:records` is thin: at most one arrow between two domains. -/
instance homSubsingleton (I J : RecDom) : Subsingleton (I ⟶ J) :=
  ⟨fun f g => by
    change PLift (J.dom ⊆ I.dom) at f g
    cases f; cases g; rfl⟩

/-- The arrow `u_{IJ} : I ⟶ J` for `J ⊆ I` (paper `sec:records`). -/
def homOfSubset {I J : RecDom} (h : J.dom ⊆ I.dom) : I ⟶ J := ⟨h⟩

/-- An arrow `I ⟶ J` of the base witnesses `J ⊆ I` (paper `sec:records`). -/
theorem subset_of_hom {I J : RecDom} (u : I ⟶ J) : J.dom ⊆ I.dom := u.down

/-- The full record domain `T = {0,1,2}` (paper `sec:records`). -/
def full : RecDom := ⟨Finset.univ, Finset.univ_nonempty⟩

/-- The singleton domain `{j}` (paper `sec:records`). -/
def single (j : Fin 3) : RecDom := ⟨{j}, Finset.singleton_nonempty j⟩

/-- The restriction arrow `T ⟶ I` from the full domain (paper `sec:records`: "`T` maps to every
    object"). -/
def fromFull (I : RecDom) : full ⟶ I := ⟨Finset.subset_univ _⟩

end RecDom

/-- The base of paper `sec:records` is connected, because `T` maps to every object. -/
instance RecDom.isConnected : IsConnected RecDom := by
  haveI : Nonempty RecDom := ⟨RecDom.full⟩
  exact zigzag_isConnected fun I J =>
    (Zigzag.of_inv (RecDom.fromFull I)).trans (Zigzag.of_hom (RecDom.fromFull J))

/-- The base of paper `sec:records` is not a groupoid: the restriction `T ⟶ {0}` is not
    invertible. -/
theorem RecDom.not_isIso_fromFull_single : ¬ IsIso (RecDom.fromFull (RecDom.single 0)) := by
  intro h
  have hsub := RecDom.subset_of_hom (inv (RecDom.fromFull (RecDom.single 0)))
  have h1 : (1 : Fin 3) ∈ (RecDom.single 0).dom := hsub (Finset.mem_univ _)
  exact absurd h1 (by decide)

/-! ## The record spaces `L(I)` and the functor `L₀` -/

/-- The record space `L(I) = {(q₀ + v j τ)_{j ∈ I} : q₀, v ∈ ℝ} ⊆ ℝ^I` (paper `sec:records`,
    "The base and its law data"). -/
def recordSpace (τ : ℝ) (I : RecDom) : Submodule ℝ (↥I.dom → ℝ) where
  carrier := {x | ∃ q₀ v : ℝ, ∀ j : ↥I.dom, x j = q₀ + v * (((j : Fin 3) : ℕ) : ℝ) * τ}
  zero_mem' := ⟨0, 0, fun j => by simp⟩
  add_mem' := by
    rintro x y ⟨a, v, hx⟩ ⟨b, w, hy⟩
    exact ⟨a + b, v + w, fun j => by simp only [Pi.add_apply, hx, hy]; ring⟩
  smul_mem' := by
    rintro c x ⟨a, v, hx⟩
    exact ⟨c * a, c * v, fun j => by simp only [Pi.smul_apply, smul_eq_mul, hx]; ring⟩

/-- Membership in the record space (paper `sec:records`). -/
theorem mem_recordSpace {τ : ℝ} {I : RecDom} {x : ↥I.dom → ℝ} :
    x ∈ recordSpace τ I ↔ ∃ q₀ v : ℝ, ∀ j : ↥I.dom, x j = q₀ + v * (((j : Fin 3) : ℕ) : ℝ) * τ :=
  Iff.rfl

/-- On the full domain `T`, the record space is cut out by the second-difference relation
    `q₂ - 2 q₁ + q₀ = 0` (paper `sec:records`, display of `L(T)`; uses `τ > 0`). -/
theorem mem_recordSpace_full_iff {τ : ℝ} (hτ : 0 < τ) (x : ↥RecDom.full.dom → ℝ) :
    x ∈ recordSpace τ RecDom.full ↔
      x ⟨2, Finset.mem_univ _⟩ - 2 * x ⟨1, Finset.mem_univ _⟩ + x ⟨0, Finset.mem_univ _⟩ = 0 := by
  constructor
  · rintro ⟨q₀, v, hx⟩
    rw [hx, hx, hx]
    simp
    ring
  · intro h
    refine ⟨x ⟨0, Finset.mem_univ _⟩, (x ⟨1, Finset.mem_univ _⟩ - x ⟨0, Finset.mem_univ _⟩) / τ,
      ?_⟩
    rintro ⟨j, hj⟩
    have hτ' : τ ≠ 0 := hτ.ne'
    fin_cases j
    · simp
    · simp
      field_simp
      ring
    · simp
      field_simp
      linarith

/-- The constant record `1` lies in every record space (paper `sec:records`: `q₀ = 1, v = 0`). -/
def recordOne (τ : ℝ) (I : RecDom) : recordSpace τ I :=
  ⟨fun _ => 1, 1, 0, fun _ => by simp⟩

/-- The constant record `1` is nonzero, since observation domains are nonempty
    (paper `sec:records`: "each `L(I)` is nonzero"). -/
theorem recordOne_ne_zero (τ : ℝ) (I : RecDom) : recordOne τ I ≠ 0 := by
  intro h
  obtain ⟨j, hj⟩ := I.nonempty
  have := congrArg (fun x : recordSpace τ I => (x : ↥I.dom → ℝ) ⟨j, hj⟩) h
  simp [recordOne] at this

/-- Every record space is nontrivial (paper `sec:records`: "each `L(I)` is nonzero"). -/
instance recordSpace_nontrivial (τ : ℝ) (I : RecDom) : Nontrivial (recordSpace τ I) :=
  ⟨⟨recordOne τ I, 0, recordOne_ne_zero τ I⟩⟩

/-- The restriction map `r_{IJ} : L(I) → L(J)` for `J ⊆ I` (paper `sec:records`). -/
def recRestrict (τ : ℝ) {I J : RecDom} (h : J.dom ⊆ I.dom) :
    recordSpace τ I →ₗ[ℝ] recordSpace τ J where
  toFun x := ⟨fun j => (x : ↥I.dom → ℝ) ⟨j.1, h j.2⟩, by
    obtain ⟨q₀, v, hx⟩ := x.2
    exact ⟨q₀, v, fun j => hx _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Values of the restriction map (paper `sec:records`): `(r_{IJ} x)_j = x_j`. -/
@[simp] theorem recRestrict_apply (τ : ℝ) {I J : RecDom} (h : J.dom ⊆ I.dom)
    (x : recordSpace τ I) (j : ↥J.dom) :
    (recRestrict τ h x : ↥J.dom → ℝ) j = (x : ↥I.dom → ℝ) ⟨j.1, h j.2⟩ := rfl

/-- Restriction commutes with scalar multiplication (paper `sec:records`: "scalar
    multiplication commutes with every restriction"). -/
theorem recRestrict_smul (τ : ℝ) {I J : RecDom} (h : J.dom ⊆ I.dom) (c : ℝ)
    (x : recordSpace τ I) : recRestrict τ h (c • x) = c • recRestrict τ h x := rfl

/-- The law functor `L : S ⥤ Vect_ℝ`, `L(I) = recordSpace τ I`, `L(u_{IJ}) = r_{IJ}`
    (paper `sec:records`). -/
def L₀ (τ : ℝ) : RecDom ⥤ ModuleCat.{0} ℝ where
  obj I := ModuleCat.of ℝ (recordSpace τ I)
  map u := ModuleCat.ofHom (recRestrict τ (RecDom.subset_of_hom u))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Objects of `L₀` (paper `sec:records`). -/
theorem L₀_obj (τ : ℝ) (I : RecDom) : (L₀ τ).obj I = ModuleCat.of ℝ (recordSpace τ I) := rfl

/-- Arrows of `L₀` are the restriction maps `r_{IJ}` (paper `sec:records`). -/
theorem L₀_map (τ : ℝ) {I J : RecDom} (u : I ⟶ J) :
    (L₀ τ).map u = ModuleCat.ofHom (recRestrict τ (RecDom.subset_of_hom u)) := rfl

/-- Values of `L₀(u_{IJ}) = r_{IJ}` (paper `sec:records`). -/
@[simp] theorem L₀_map_hom_apply (τ : ℝ) {I J : RecDom} (u : I ⟶ J) (x : recordSpace τ I)
    (j : ↥J.dom) :
    Subtype.val (((L₀ τ).map u).hom x) j
      = (x : ↥I.dom → ℝ) ⟨j.1, RecDom.subset_of_hom u j.2⟩ :=
  rfl

/-- Each `L(I)` is nonzero (paper `sec:records`). -/
instance L₀_obj_nontrivial (τ : ℝ) (I : RecDom) : Nontrivial ((L₀ τ).obj I) :=
  recordSpace_nontrivial τ I

/-- Each `L(I)` contains a nonzero record (paper `sec:records`). -/
theorem L₀_exists_ne_zero (τ : ℝ) (I : RecDom) : ∃ x : (L₀ τ).obj I, x ≠ 0 :=
  ⟨recordOne τ I, recordOne_ne_zero τ I⟩

/-! ## Labeled observation spaces -/

/-- The labeling functor `S ⥤ Pair S`, `I ↦ ⟨I⟩` (paper `sec:records`, "explicitly labeled
    vector spaces": the label of `L(I)` is its observation domain `I`). -/
def recLabel : RecDom ⥤ Pair RecDom where
  obj I := ⟨I⟩
  map _ := ⟨⟩

/-- The labeled law functor (paper `sec:records`, "For these explicitly labeled vector spaces"):
    `Lℓ(I) = (⟨I⟩, L(I))` in `Pair S × Vect_ℝ`, `Lℓ(u_{IJ}) = (*, r_{IJ})`. -/
def Lℓ (τ : ℝ) : CategoryTheory.Functor.{0, 0} RecDom (Pair RecDom × ModuleCat.{0} ℝ) :=
  recLabel.prod' (L₀ τ)

/-- Forgetting the labels recovers the unlabeled law functor (paper `sec:records`). -/
theorem Lℓ_comp_snd (τ : ℝ) : Lℓ τ ⋙ CategoryTheory.Prod.snd _ _ = L₀ τ := rfl

/-- The label of `Lℓ(I)` is `I` (paper `sec:records`). -/
theorem Lℓ_obj_fst (τ : ℝ) (I : RecDom) : ((Lℓ τ).obj I).1 = ⟨I⟩ := rfl

/-! ## The presentation `O = S × Pair(G)` with `G = ℤˣ` -/

/-- The normalized presentation datum of paper `sec:records` ("Presentations and their
    comparisons"): `O = S × Pair(G)` with `G = ℤˣ = {+1, -1}`, `p(I, ε) = I`. -/
abbrev recData : OEData ℤˣ (CategoryTheory.Prod.fst RecDom (Pair ℤˣ)) :=
  productData RecDom ℤˣ

/-- The action of the presentation (paper `sec:records`): `(I, ε) · h = (I, ε h)`. -/
theorem recData_act (I : RecDom) (ε h : ℤˣ) : recData.act (I, ⟨ε⟩) h = (I, ⟨ε * h⟩) := rfl

/-- The basepoints of the presentation (paper `sec:records`): `b_I = (I, +1)`. -/
theorem recData_base (I : RecDom) : recData.base I = (I, ⟨1⟩) := rfl

/-- The reindexing of the presentation (paper `sec:records`): `u_{IJ}^* (J, δ) = (I, δ)`. -/
theorem recData_reind {I J : RecDom} (u : I ⟶ J) (δ : ℤˣ) :
    recData.reind u (J, ⟨δ⟩) rfl = (I, ⟨δ⟩) := rfl

/-! ## Signs acting on real vector spaces -/

/-- The real scalar of a sign `ε ∈ ℤˣ` is multiplicative (paper `sec:records`, signs act on
    records by `((ε : ℤ) : ℝ) • ·`). -/
theorem recSign_mul (ε δ : ℤˣ) :
    (((ε * δ : ℤˣ) : ℤ) : ℝ) = ((ε : ℤ) : ℝ) * ((δ : ℤ) : ℝ) := by
  push_cast; ring

/-- A sign squares to one (paper `sec:records`). -/
theorem recSign_mul_self (ε : ℤˣ) : ((ε : ℤ) : ℝ) * ((ε : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-- A sign is its own inverse (paper `sec:records`: `ε⁻¹ = ε`). -/
theorem recSign_inv (ε : ℤˣ) : (((ε⁻¹ : ℤˣ) : ℤ) : ℝ) = ((ε : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-- The scalar of `+1` (paper `sec:records`). -/
theorem recSign_one : (((1 : ℤˣ) : ℤ) : ℝ) = 1 := by norm_num

/-- The scalar of `-1` (paper `sec:records`). -/
theorem recSign_neg_one : (((-1 : ℤˣ) : ℤ) : ℝ) = -1 := by norm_num

/-- A sign scalar is nonzero (paper `sec:records`). -/
theorem recSign_ne_zero (ε : ℤˣ) : ((ε : ℤ) : ℝ) ≠ 0 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num

/-! ## The reflection `ρ(j) = 2 - j` and the base involution `A` -/

/-- The time reflection `ρ(j) = 2 - j` on `T = {0,1,2}` (paper `sec:records`, "A base symmetry
    and its implementation"), realized as `Fin.rev`. -/
def recρ : Fin 3 → Fin 3 := Fin.rev

/-- `ρ(j) = 2 - j` as real numbers (paper `sec:records`). -/
theorem recρ_cast (j : Fin 3) : (((recρ j : Fin 3) : ℕ) : ℝ) = 2 - (((j : Fin 3) : ℕ) : ℝ) := by
  fin_cases j <;> norm_num [recρ]

/-- `ρ` is an involution (paper `sec:records`). -/
theorem recρ_recρ (j : Fin 3) : recρ (recρ j) = j := Fin.rev_rev j

/-- The relabeled domain `ρ(I)` (paper `sec:records`: `A(I) = ρ(I)`). -/
def RecDom.rev (I : RecDom) : RecDom :=
  ⟨I.dom.map Fin.revPerm.toEmbedding, I.nonempty.map⟩

/-- Membership in `ρ(I)` (paper `sec:records`): `j ∈ ρ(I) ↔ ρ(j) ∈ I`. -/
theorem RecDom.mem_rev {I : RecDom} {j : Fin 3} : j ∈ I.rev.dom ↔ recρ j ∈ I.dom := by
  simp [RecDom.rev, Finset.mem_map_equiv, Fin.revPerm_symm, recρ]

/-- `ρ(ρ(I)) = I` (paper `sec:records`). -/
theorem RecDom.rev_rev (I : RecDom) : I.rev.rev = I := by
  ext j
  rw [RecDom.mem_rev, RecDom.mem_rev, recρ_recρ]

/-- The functor `A : S ⥤ S`, `I ↦ ρ(I)` (paper `sec:records`). -/
def recAFunctor : RecDom ⥤ RecDom where
  obj I := I.rev
  map u := RecDom.homOfSubset fun j hj =>
    RecDom.mem_rev.2 (RecDom.subset_of_hom u (RecDom.mem_rev.1 hj))

/-- `A ⋙ A = 𝟭` on the nose (paper `sec:records`: `A` is an involution). -/
theorem recAFunctor_comp_self : recAFunctor ⋙ recAFunctor = 𝟭 RecDom :=
  CategoryTheory.Functor.ext (fun I => RecDom.rev_rev I) (fun _ _ _ => Subsingleton.elim _ _)

/-- The strict base automorphism `A(I) = ρ(I)` (paper `sec:records`). -/
def recA : StrictAut RecDom :=
  ⟨recAFunctor, recAFunctor, recAFunctor_comp_self, recAFunctor_comp_self⟩

/-- `A(I) = ρ(I)` (paper `sec:records`). -/
theorem recA_hom_obj (I : RecDom) : recA.hom.obj I = I.rev := rfl

/-- `A² = 1` (paper `sec:records`). -/
theorem recA_mul_self : recA * recA = 1 :=
  StrictAut.ext recAFunctor_comp_self recAFunctor_comp_self

/-- `A⁻¹ = A` (paper `sec:records`). -/
theorem recA_inv : recA⁻¹ = recA := inv_eq_of_mul_eq_one_right recA_mul_self

/-- `ρ({0}) = {2}` (paper `sec:records`: "the singleton domains `{0}` and `{2}` differ"). -/
theorem RecDom.rev_single_zero : (RecDom.single 0).rev = RecDom.single 2 := by
  ext j
  rw [RecDom.mem_rev]
  fin_cases j <;> decide

/-- `A ≠ 1`: it moves `{0}` to `{2}` (paper `sec:records`). -/
theorem recA_ne_one : recA ≠ 1 := by
  intro h
  have h0 := congrArg (fun B : StrictAut RecDom => B.hom.obj (RecDom.single 0)) h
  simp only [recA_hom_obj, RecDom.rev_single_zero, StrictAut.one_hom, Functor.id_obj] at h0
  have h2 : (2 : Fin 3) ∈ (RecDom.single 2).dom := Finset.mem_singleton_self _
  rw [h0] at h2
  exact absurd h2 (by decide)

/-! ## The selected subgroup `H = {1, A} ≅ C₂` -/

namespace RecordsExample

section C2

variable {A B : Type*} [Group A] [Group B]

/-- A homomorphism out of a group `{1, a}` of order at most two, sending `a` to an involution
    `b` (helper for paper `sec:records`, `H ≅ C₂`). -/
def c2Hom [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1) (haa : a * a = 1)
    (b : B) (hbb : b * b = 1) : A →* B where
  toFun x := if x = 1 then 1 else b
  map_one' := if_pos rfl
  map_mul' x y := by
    rcases hA x with rfl | rfl <;> rcases hA y with rfl | rfl <;> simp [ha, haa, hbb]

/-- `c2Hom` sends `1` to `1` (helper for paper `sec:records`). -/
@[simp] theorem c2Hom_one' [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1)
    (haa : a * a = 1) (b : B) (hbb : b * b = 1) : c2Hom a hA ha haa b hbb 1 = 1 :=
  if_pos rfl

/-- `c2Hom` sends the generator to `b` (helper for paper `sec:records`). -/
@[simp] theorem c2Hom_gen [DecidableEq A] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1)
    (haa : a * a = 1) (b : B) (hbb : b * b = 1) : c2Hom a hA ha haa b hbb a = b :=
  if_neg ha

/-- Groups `{1, a}`, `{1, b}` of order exactly two are isomorphic via `a ↦ b` (helper for paper
    `sec:records`: `H ≅ C₂` and `G = {±1} ≅ C₂`). -/
def c2MulEquiv [DecidableEq A] [DecidableEq B] (a : A) (hA : ∀ x : A, x = 1 ∨ x = a)
    (ha : a ≠ 1) (haa : a * a = 1) (b : B) (hB : ∀ y : B, y = 1 ∨ y = b) (hb : b ≠ 1)
    (hbb : b * b = 1) : A ≃* B :=
  { c2Hom a hA ha haa b hbb with
    invFun := c2Hom b hB hb hbb a haa
    left_inv := fun x => by
      rcases hA x with rfl | rfl
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_one']
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_gen]
    right_inv := fun y => by
      rcases hB y with rfl | rfl
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_one']
      · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, c2Hom_gen] }

/-- `c2MulEquiv` sends the generator to the generator (helper for paper `sec:records`). -/
@[simp] theorem c2MulEquiv_gen [DecidableEq A] [DecidableEq B] (a : A)
    (hA : ∀ x : A, x = 1 ∨ x = a) (ha : a ≠ 1) (haa : a * a = 1) (b : B)
    (hB : ∀ y : B, y = 1 ∨ y = b) (hb : b ≠ 1) (hbb : b * b = 1) :
    c2MulEquiv a hA ha haa b hB hb hbb a = b :=
  if_neg ha

end C2

/-- The generator of `C₂ = Multiplicative (ZMod 2)` (paper `sec:records`). -/
def c2Gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

/-- Every element of `C₂` is `1` or the generator (paper `sec:records`). -/
theorem c2_cases : ∀ k : Multiplicative (ZMod 2), k = 1 ∨ k = c2Gen := by decide

/-- The generator of `C₂` is nontrivial (paper `sec:records`). -/
theorem c2Gen_ne_one : c2Gen ≠ 1 := by decide

/-- The generator of `C₂` is an involution (paper `sec:records`). -/
theorem c2Gen_mul_self : c2Gen * c2Gen = 1 := by decide

end RecordsExample

open RecordsExample

/-- The selected base group `H = {1, A} = ⟨A⟩ ≤ Aut(S)` (paper `sec:records`). -/
def recH : Subgroup (StrictAut RecDom) := Subgroup.zpowers recA

/-- The elements of `H` are exactly `1` and `A` (paper `sec:records`: `H = {1, A}`). -/
theorem mem_recH {B : StrictAut RecDom} : B ∈ recH ↔ B = 1 ∨ B = recA := by
  constructor
  · intro hB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hB
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, recA_mul_self, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, recA_mul_self, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

/-- `A` as an element of `H` (paper `sec:records`). -/
def recHA : recH := ⟨recA, Subgroup.mem_zpowers _⟩

/-- Every element of `H` is `1` or `A` (paper `sec:records`). -/
theorem recH_cases (B : recH) : B = 1 ∨ B = recHA := by
  rcases mem_recH.1 B.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- `A ≠ 1` in `H` (paper `sec:records`). -/
theorem recHA_ne_one : recHA ≠ 1 := fun h => recA_ne_one (congrArg Subtype.val h)

/-- `A² = 1` in `H` (paper `sec:records`). -/
theorem recHA_mul_self : recHA * recHA = 1 := Subtype.ext recA_mul_self

open Classical in
/-- `H = {1, A} ≅ C₂ = Multiplicative (ZMod 2)`, `A ↦ ofAdd 1` (paper `sec:records`). -/
noncomputable def recHMulEquiv : recH ≃* Multiplicative (ZMod 2) :=
  c2MulEquiv recHA recH_cases recHA_ne_one recHA_mul_self
    c2Gen c2_cases c2Gen_ne_one c2Gen_mul_self

/-- `H` has order two (paper `sec:records`: `H ≅ C₂`). -/
theorem recH_card : Nat.card recH = 2 := by
  rw [Nat.card_congr recHMulEquiv.toEquiv, Nat.card_eq_fintype_card]
  rfl

/-- The sign group `G = ℤˣ = {+1, -1} ≅ C₂`, `-1 ↦ ofAdd 1` (paper `sec:records`). -/
def recSignMulEquiv : ℤˣ ≃* Multiplicative (ZMod 2) :=
  c2MulEquiv (-1) (fun u => Int.units_eq_one_or u) (by decide) (by decide)
    c2Gen c2_cases c2Gen_ne_one c2Gen_mul_self

/-! ## The selected lift group `Sym_H(p) ≅ C₂ × C₂` -/

/-- The canonical lift of `A` is `Ã(I, ε) = (ρ(I), ε)` (paper `sec:records`). -/
theorem recLift_obj (I : RecDom) (ε : ℤˣ) :
    (liftHomOver recData recH recHA).1.hom.obj (I, ⟨ε⟩) = (I.rev, ⟨ε⟩) := by
  show ((I.rev, ⟨1 * ε⟩) : RecDom × Pair ℤˣ) = (I.rev, ⟨ε⟩)
  rw [one_mul]

/-- The global polarity change `Λ_h(I, ε) = (I, h ε)` (paper `sec:records`). -/
theorem recPolarity_obj (h : ℤˣ) (I : RecDom) (ε : ℤˣ) :
    (ΛHomOver recData recH h).1.hom.obj (I, ⟨ε⟩) = (I, ⟨h * ε⟩) := by
  show ((I, ⟨1 * (h * ε)⟩) : RecDom × Pair ℤˣ) = (I, ⟨h * ε⟩)
  rw [one_mul]

/-- The canonical lift of `A` commutes with the global polarity change (paper `sec:records`). -/
theorem recLift_comm_polarity (h : ℤˣ) :
    ΛHomOver recData recH h * liftHomOver recData recH recHA
      = liftHomOver recData recH recHA * ΛHomOver recData recH h :=
  ΛHomOver_comm_liftHomOver recData recH h recHA

/-- The selected lift group as a direct product, `Sym_H(p) ≅ G × H` (paper `sec:records`, via
    `thm:strict` for the connected base `S`). -/
noncomputable def recSymProd : AutBoxGOver recData recH ≃* ℤˣ × recH :=
  autBoxGOverMulEquivProd recData recH

/-- The selected lift group `Sym_H(p) ≅ C₂ × C₂` (paper `sec:records`). -/
noncomputable def recSym :
    AutBoxGOver recData recH ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  recSymProd.trans (MulEquiv.prodCongr recSignMulEquiv recHMulEquiv)

/-! ## Labeled law data: `LA ≠ L` strictly -/

/-- For the explicitly labeled law functor, `L A ≠ L` strictly (paper `sec:records`: "already the
    singleton domains `{0}` and `{2}` differ"): the label of `(L A)({0})` is `ρ({0}) = {2}`,
    while the label of `L({0})` is `{0}`. -/
theorem recA_comp_Lℓ_ne (τ : ℝ) : recA.hom ⋙ Lℓ τ ≠ Lℓ τ := by
  intro h
  have h0 := congrArg (fun F : RecDom ⥤ Pair RecDom × ModuleCat.{0} ℝ =>
    ((F.obj (RecDom.single 0)).1.pt).dom) h
  change (RecDom.single 0).rev.dom = (RecDom.single 0).dom at h0
  rw [RecDom.rev_single_zero] at h0
  have h2 : (2 : Fin 3) ∈ (RecDom.single 2).dom := Finset.mem_singleton_self _
  rw [h0] at h2
  exact absurd h2 (by decide)

/-- `A` is not in the strict stabilizer of the labeled law (paper `sec:records`, `def:law`). -/
theorem recA_not_mem_strictLawStabilizer (τ : ℝ) : recA ∉ strictLawStabilizer (Lℓ τ) :=
  recA_comp_Lℓ_ne τ

/-- The selected group `H` is not contained in the strict stabilizer of the labeled law
    (paper `sec:records`: `H` is "not the strict stabilizer `H_L`"). -/
theorem recH_not_le_strictLawStabilizer (τ : ℝ) : ¬ recH ≤ strictLawStabilizer (Lℓ τ) :=
  fun hle => recA_not_mem_strictLawStabilizer τ (hle (Subgroup.mem_zpowers recA))

/-- The strict stabilizer of the labeled law is trivial (paper `sec:records`, `def:law`): labels
    force `A(I) = I` for all `I`, and the base is thin. -/
theorem strictLawStabilizer_Lℓ_eq_bot (τ : ℝ) : strictLawStabilizer (Lℓ τ) = ⊥ := by
  ext B
  simp only [Subgroup.mem_bot]
  constructor
  · intro hB
    have hB' : B.hom ⋙ Lℓ τ = Lℓ τ := hB
    have hobj : ∀ I, B.hom.obj I = I := fun I => by
      have := congrArg (fun F : RecDom ⥤ Pair RecDom × ModuleCat.{0} ℝ => (F.obj I).1.pt) hB'
      exact this
    exact StrictAut.ext_hom (CategoryTheory.Functor.ext hobj (fun _ _ _ => Subsingleton.elim _ _))
  · rintro rfl
    exact one_mem _

/-! ## Unlabeled law data: `LA ≠ L` strictly -/

/-- The index record `x_j = j` in `L(I)` (`q₀ = 0`, `v = 1/τ`, needs `τ ≠ 0`), used to show
    `L A ≠ L` for the unlabeled law (paper `sec:records`). -/
noncomputable def recIdxRecord (τ : ℝ) (hτ : τ ≠ 0) (I : RecDom) : recordSpace τ I :=
  ⟨fun j => (((j : Fin 3) : ℕ) : ℝ), 0, 1 / τ, fun j => by field_simp; ring⟩

/-- Values of a cast `eqToHom e` between record spaces `L(I) = L(I')` over `I = I'`: the cast
    keeps entries (helper for paper `sec:records`; the proof `e` is arbitrary). -/
theorem L₀_eqToHom_hom_apply_of_eq (τ : ℝ) {I I' : RecDom} (hI : I = I')
    (e : (L₀ τ).obj I = (L₀ τ).obj I') (x : recordSpace τ I) (j : ↥I'.dom) :
    Subtype.val ((eqToHom e).hom x) j = (x : ↥I.dom → ℝ) ⟨j.1, by subst hI; exact j.2⟩ := by
  subst hI; rfl

/-- For the unlabeled law functor `L = L₀ τ` (`τ ≠ 0`), `L A ≠ L` strictly (paper `sec:records`:
    "already the singleton domains `{0}` and `{2}` differ"). An equality of functors would give
    `r_{ρ(T)ρ({0})} = c₁ ≫ r_{T{0}} ≫ c₂` with linear casts `cᵢ`. On the record `x_j = j`, the
    left side takes the value `2` at the index `2 ∈ ρ({0})`, and the right side is `c₂(0) = 0`.
    No equality of carrier types is decided. -/
theorem recA_comp_L₀_ne (τ : ℝ) (hτ : τ ≠ 0) : recA.hom ⋙ L₀ τ ≠ L₀ τ := by
  intro h
  have key := Functor.congr_hom h (RecDom.fromFull (RecDom.single 0))
  have hf : recA.hom.obj RecDom.full = RecDom.full := by
    ext j; simp [recA_hom_obj, RecDom.rev, RecDom.full]
  have h2mem : (2 : Fin 3) ∈ (recA.hom.obj (RecDom.single 0)).dom := by
    rw [recA_hom_obj, RecDom.mem_rev]; decide
  have e := congrArg (fun k : (recA.hom ⋙ L₀ τ).obj RecDom.full ⟶
      (recA.hom ⋙ L₀ τ).obj (RecDom.single 0) =>
    Subtype.val (k.hom (recIdxRecord τ hτ _)) ⟨2, h2mem⟩) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  have hz : ((L₀ τ).map (RecDom.fromFull (RecDom.single 0))).hom
      ((eqToHom (Functor.congr_obj h RecDom.full)).hom (recIdxRecord τ hτ _)) = 0 := by
    apply Subtype.ext; funext j
    obtain ⟨j, hj⟩ := j
    have : j = 0 := Finset.mem_singleton.1 hj
    subst this
    rw [L₀_map_hom_apply]
    have := L₀_eqToHom_hom_apply_of_eq τ hf (Functor.congr_obj h RecDom.full)
      (recIdxRecord τ hτ _) ⟨0, Finset.mem_univ _⟩
    erw [this]
    simp [recIdxRecord]; rfl
  rw [hz, map_zero] at e
  change (2 : ℝ) = 0 at e
  norm_num at e

/-- `A` is not in the strict stabilizer `H_L` of the unlabeled law `L = L₀ τ`, `τ ≠ 0` (paper
    `sec:records`, `def:law`). -/
theorem recA_not_mem_strictLawStabilizer_L₀ (τ : ℝ) (hτ : τ ≠ 0) :
    recA ∉ strictLawStabilizer (L₀ τ) :=
  recA_comp_L₀_ne τ hτ

/-- The selected group `H` is not contained in the strict stabilizer of the unlabeled law
    (paper `sec:records`: `H` is "not the strict stabilizer `H_L`"). -/
theorem recH_not_le_strictLawStabilizer_L₀ (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ recH ≤ strictLawStabilizer (L₀ τ) :=
  fun hle => recA_not_mem_strictLawStabilizer_L₀ τ hτ (hle (Subgroup.mem_zpowers recA))

/-! ## The covariant implementation `α : L A ≅ L` -/

/-- Time reversal of records, `(α_I x)_j = x_{ρ(j)}`, as a linear isomorphism
    `L(ρ(I)) ≃ L(I)` (paper `sec:records`, "A base symmetry and its implementation"). The
    reversed affine record `q₀ + v (2 - j) τ = (q₀ + 2 v τ) - v j τ` is again affine. -/
def recRevEquiv (τ : ℝ) (I : RecDom) : recordSpace τ I.rev ≃ₗ[ℝ] recordSpace τ I where
  toFun x := ⟨fun j => (x : ↥I.rev.dom → ℝ) ⟨recρ j.1, by rw [RecDom.mem_rev, recρ_recρ]; exact j.2⟩,
    by
      obtain ⟨q₀, v, hx⟩ := x.2
      refine ⟨q₀ + 2 * v * τ, -v, fun j => ?_⟩
      simp only [hx, recρ_cast]
      ring⟩
  invFun y := ⟨fun k => (y : ↥I.dom → ℝ) ⟨recρ k.1, RecDom.mem_rev.1 k.2⟩,
    by
      obtain ⟨q₀, v, hy⟩ := y.2
      refine ⟨q₀ + 2 * v * τ, -v, fun k => ?_⟩
      simp only [hy, recρ_cast]
      ring⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (funext fun k => congrArg (x : ↥I.rev.dom → ℝ)
    (Subtype.ext (recρ_recρ k.1)))
  right_inv y := Subtype.ext (funext fun j => congrArg (y : ↥I.dom → ℝ)
    (Subtype.ext (recρ_recρ j.1)))

/-- Values of the time-reversal isomorphism (paper `sec:records`): `(α_I x)_j = x_{ρ(j)}`. -/
theorem recRevEquiv_apply (τ : ℝ) (I : RecDom) (x : recordSpace τ I.rev) (j : ↥I.dom) :
    (recRevEquiv τ I x : ↥I.dom → ℝ) j
      = (x : ↥I.rev.dom → ℝ) ⟨recρ j.1, by rw [RecDom.mem_rev, recρ_recρ]; exact j.2⟩ := rfl

/-- The covariant implementation of the base symmetry: the natural linear isomorphism
    `α : L A ≅ L`, `α_I : L(ρ(I)) → L(I)`, `(α_I x)_j = x_{ρ(j)}` (paper `sec:records`).
    Naturality is "the maps `α_I` commute with restrictions". -/
noncomputable def recα (τ : ℝ) : recA.hom ⋙ L₀ τ ≅ L₀ τ :=
  NatIso.ofComponents (fun I => (recRevEquiv τ I).toModuleIso) (fun _ => rfl)

/-- Values of the covariant implementation (paper `sec:records`): `(α_I x)_j = x_{ρ(j)}`. -/
theorem recα_hom_app_apply (τ : ℝ) (I : RecDom) (x : recordSpace τ I.rev) (j : ↥I.dom) :
    Subtype.val (((recα τ).hom.app I).hom x) j
      = (x : ↥I.rev.dom → ℝ) ⟨recρ j.1, by rw [RecDom.mem_rev, recρ_recρ]; exact j.2⟩ := rfl

/-- The maps `α_I` commute with restrictions (paper `sec:records`): for `u : I ⟶ J`,
    `r_{IJ} ∘ α_I = α_J ∘ r_{ρ(I)ρ(J)}`. -/
theorem recα_naturality (τ : ℝ) {I J : RecDom} (u : I ⟶ J) :
    (L₀ τ).map (recA.hom.map u) ≫ (recα τ).hom.app J = (recα τ).hom.app I ≫ (L₀ τ).map u :=
  (recα τ).hom.naturality u

/-- `A(A(I)) = I` (paper `sec:records`). -/
theorem recA_hom_obj_obj (I : RecDom) : recA.hom.obj (recA.hom.obj I) = I := RecDom.rev_rev I

/-- Entries of a record at equal indices agree (helper for paper `sec:records`). -/
theorem recordSpace_val_congr {τ : ℝ} {I : RecDom} (x : recordSpace τ I) {j k : Fin 3}
    (hj : j ∈ I.dom) (hk : k ∈ I.dom) (h : j = k) :
    (x : ↥I.dom → ℝ) ⟨j, hj⟩ = (x : ↥I.dom → ℝ) ⟨k, hk⟩ := by
  subst h; rfl

/-- Values of the `L₀`-image of an object equality (helper for paper `sec:records`). -/
theorem L₀_eqToHom_hom_apply (τ : ℝ) {I I' : RecDom} (h : I = I') (x : recordSpace τ I)
    (j : ↥I'.dom) :
    Subtype.val ((eqToHom (congrArg (L₀ τ).obj h)).hom x) j
      = (x : ↥I.dom → ℝ) ⟨j.1, by subst h; exact j.2⟩ := by
  subst h; rfl

/-- Involution coherence of the covariant implementation (paper `sec:records`):
    `α_I ∘ α_{ρ(I)} = id`, up to the object equality `ρ(ρ(I)) = I`. -/
theorem recα_involution (τ : ℝ) (I : RecDom) :
    ((recα τ).hom.app (recA.hom.obj I) ≫ (recα τ).hom.app I :
        (L₀ τ).obj (recA.hom.obj (recA.hom.obj I)) ⟶ (L₀ τ).obj I)
      = eqToHom (congrArg (L₀ τ).obj (recA_hom_obj_obj I)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext j
  rw [L₀_eqToHom_hom_apply τ (recA_hom_obj_obj I)]
  exact recordSpace_val_congr x _ _ (recρ_recρ j.1)

/-- Pointwise involution coherence (paper `sec:records`): `(α_I (α_{ρ(I)} x))_j = x_j`, where
    `j ∈ I = ρ(ρ(I))`. -/
theorem recα_involution_apply (τ : ℝ) (I : RecDom) (x : recordSpace τ I.rev.rev) (j : ↥I.dom) :
    Subtype.val (((recα τ).hom.app I).hom (((recα τ).hom.app (recA.hom.obj I)).hom x)) j
      = (x : ↥I.rev.rev.dom → ℝ) ⟨j.1, by rw [RecDom.rev_rev]; exact j.2⟩ :=
  recordSpace_val_congr x _ _ (recρ_recρ j.1)

/-- `A ⋙ A ⋙ L = L` (paper `sec:records`). -/
theorem recA_hom_comp_self_comp_L₀ (τ : ℝ) : recA.hom ⋙ recA.hom ⋙ L₀ τ = L₀ τ := by
  rw [← Functor.assoc]
  exact congrArg (· ⋙ L₀ τ) recAFunctor_comp_self

/-- Involution coherence at the level of natural transformations (paper `sec:records`):
    `α ∘ (α A) = id` up to `A A = 𝟭`. -/
theorem recα_involution_natTrans (τ : ℝ) :
    Functor.whiskerLeft recA.hom (recα τ).hom ≫ (recα τ).hom
      = eqToHom (recA_hom_comp_self_comp_L₀ τ) := by
  apply NatTrans.ext
  funext I
  rw [eqToHom_app, NatTrans.comp_app]
  exact recα_involution τ I

/-- The label isomorphism `⟨ρ(I)⟩ ≅ ⟨I⟩` in `Pair S` (paper `sec:records`, labeled spaces). -/
def recLabelIso (I J : RecDom) : (⟨I⟩ : Pair RecDom) ≅ ⟨J⟩ where
  hom := ⟨⟩
  inv := ⟨⟩

/-- The covariant implementation on labeled spaces, `αℓ : L A ≅ L` in `Pair S × Vect_ℝ`,
    relabeling `ρ(I)` to `I` and acting by `α_I` on records (paper `sec:records`). -/
noncomputable def recαℓ (τ : ℝ) : recA.hom ⋙ Lℓ τ ≅ Lℓ τ :=
  NatIso.ofComponents (fun I => Iso.prod (recLabelIso I.rev I) (recRevEquiv τ I).toModuleIso)
    (fun _ => rfl)

/-- The record component of `αℓ` is `α` (paper `sec:records`). -/
theorem recαℓ_hom_app_snd (τ : ℝ) (I : RecDom) :
    ((recαℓ τ).hom.app I).2 = (recα τ).hom.app I := rfl

/-- The record component of the `Lℓ`-image of an object equality is the `L₀`-image (helper for
    paper `sec:records`, labeled spaces). -/
theorem Lℓ_eqToHom_snd (τ : ℝ) {I I' : RecDom} (h : I = I') :
    (eqToHom (congrArg (Lℓ τ).obj h)).2 = eqToHom (congrArg (L₀ τ).obj h) := by
  subst h; rfl

/-- Involution coherence of the covariant implementation on labeled spaces (paper
    `sec:records`): `αℓ_I ∘ αℓ_{ρ(I)} = id`, up to the object equality `ρ(ρ(I)) = I`. The label
    component is trivial and the record component is `recα_involution`. -/
theorem recαℓ_involution (τ : ℝ) (I : RecDom) :
    ((recαℓ τ).hom.app (recA.hom.obj I) ≫ (recαℓ τ).hom.app I :
        (Lℓ τ).obj (recA.hom.obj (recA.hom.obj I)) ⟶ (Lℓ τ).obj I)
      = eqToHom (congrArg (Lℓ τ).obj (recA_hom_obj_obj I)) := by
  refine Prod.ext (Subsingleton.elim _ _) ?_
  rw [prod_comp_snd, Lℓ_eqToHom_snd τ (recA_hom_obj_obj I)]
  exact recα_involution τ I
