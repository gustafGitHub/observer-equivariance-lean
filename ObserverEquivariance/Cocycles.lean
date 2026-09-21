import Mathlib

/-!
# Nonabelian 1-cocycles, sections and complements of a fixed split extension

Pure group theory behind the cocycle paragraph at the end of `sec:normalization` of the paper
(the discussion after `prop:basechange`): the factor `z_c(A) = c θ_A(c⁻¹)`, nonabelian
`1`-coboundaries, `H¹(H,G)`, and its interpretation through sections and complements of the
**fixed** split extension `G ⋊_θ H`.

Throughout, `G` and `H` are arbitrary (not necessarily commutative) groups and
`θ : H →* MulAut G`. The convention is the paper's:

* a cocycle is `z : H → G` with `z (A * B) = z A * θ A (z B)`;
* `z` and `z'` are cohomologous if `z' A = c * z A * θ A c⁻¹` for some `c : G`.

## Paper labels covered

* `sec:normalization` (cocycle paragraph): `coboundary_mul` (`z_c(AB) = z_c(A) θ_A(z_c(B))`),
  `coboundary` is cohomologous to the trivial cocycle (`cohomologous_one_coboundary`,
  `H1.mk_coboundary`), the cocycle / section correspondence `A ↦ (z(A), A)`
  (`cocycleSectionEquiv`), the cohomology relation is conjugation by `(c, 1)`
  (`conj_inl_section`, `cohomologous_iff_sectionConj`), `H¹(H,G)` classifies sections, equivalently
  complements to the kernel, up to conjugation by `G` (`H1EquivSectionClasses`,
  `section_range_isComplement`, `sectionComplementEquiv`, `H1EquivComplementClasses`).
* INSTR §5 (end): same content.

## Scope (what `H1` is and is not)

For nonabelian `G`, `H1 θ` is only a **pointed set** (basepoint: the class of the trivial cocycle),
not a group. It classifies group-hom sections of `SemidirectProduct.rightHom : G ⋊[θ] H →* H`, and
equivalently complements of the kernel `SemidirectProduct.inl.range`, **up to conjugation by
`G`** (i.e. by the kernel). It does **not** classify extensions of `H` by `G`: the extension
`G ⋊[θ] H` is fixed throughout.

mathlib's `groupCohomology` has `IsMulCocycle₁` / `IsMulCoboundary₁` / `groupCohomology.H1`, but
for commutative coefficients (a `Rep`/`CommGroup` with a `MulAction`) and a different
multiplication order; we keep our own nonabelian statements in the namespace `OECocycle`.
-/

namespace OECocycle

open SemidirectProduct

variable {G H : Type*} [Group G] [Group H] (θ : H →* MulAut G)

/-! ### Coboundaries and cocycles -/

/-- The nonabelian `1`-coboundary `z_c(A) = c θ_A(c⁻¹)` of `c : G`
(paper `sec:normalization`, cocycle paragraph). -/
def coboundary (c : G) (A : H) : G := c * θ A c⁻¹

/-- The coboundary identity `z_c(AB) = z_c(A) θ_A(z_c(B))`
(paper `sec:normalization`, cocycle paragraph). -/
theorem coboundary_mul (c : G) (A B : H) :
    coboundary θ c (A * B) = coboundary θ c A * θ A (coboundary θ c B) := by
  simp only [coboundary, map_mul, MulAut.mul_apply, map_inv, mul_assoc, inv_mul_cancel_left]

/-- `z : H → G` is a (nonabelian, left) `1`-cocycle for `θ`: `z(AB) = z(A) θ_A(z(B))`
(paper `sec:normalization`, cocycle paragraph). -/
def IsCocycle (z : H → G) : Prop := ∀ A B : H, z (A * B) = z A * θ A (z B)

variable {θ} in
/-- A cocycle is normalized: `z 1 = 1` (paper `sec:normalization`, cocycle paragraph). -/
theorem IsCocycle.apply_one {z : H → G} (hz : IsCocycle θ z) : z 1 = 1 := by
  have h := hz 1 1
  simp only [mul_one, map_one, MulAut.one_apply] at h
  simpa using h

/-- Every coboundary `z_c` is a cocycle (paper `sec:normalization`, cocycle paragraph). -/
theorem isCocycle_coboundary (c : G) : IsCocycle θ (coboundary θ c) :=
  fun A B => coboundary_mul θ c A B

/-- The trivial cocycle `A ↦ 1` (paper `sec:normalization`, cocycle paragraph). -/
theorem isCocycle_one : IsCocycle θ (fun _ : H => (1 : G)) := by
  intro A B
  simp

/-- The type of cocycles `{z : H → G // IsCocycle θ z}`
(paper `sec:normalization`, cocycle paragraph). -/
abbrev Cocycle := {z : H → G // IsCocycle θ z}

/-- The type of group-hom sections of `rightHom : G ⋊[θ] H →* H` of the **fixed** split extension
(paper `sec:normalization`, cocycle paragraph). -/
abbrev SemidirectSection := {σ : H →* G ⋊[θ] H // ∀ A, (σ A).right = A}

/-! ### Cocycles are sections -/

variable {θ} in
/-- The section `A ↦ (z(A), A)` defined by a cocycle `z`
(paper `sec:normalization`, cocycle paragraph). -/
def cocycleSection {z : H → G} (hz : IsCocycle θ z) : H →* G ⋊[θ] H where
  toFun A := ⟨z A, A⟩
  map_one' := by
    ext
    · simp [hz.apply_one]
    · rfl
  map_mul' A B := by
    ext
    · simp [SemidirectProduct.mul_left, hz A B]
    · rfl

/-- Cocycles correspond bijectively to group-hom sections of `rightHom` of the fixed extension
`G ⋊[θ] H`, via `z ↦ (A ↦ (z(A), A))` and `σ ↦ (A ↦ (σ A).left)`
(paper `sec:normalization`, cocycle paragraph). -/
def cocycleSectionEquiv :
    {z : H → G // IsCocycle θ z} ≃ {σ : H →* G ⋊[θ] H // ∀ A, (σ A).right = A} where
  toFun z := ⟨cocycleSection z.2, fun _ => rfl⟩
  invFun σ := ⟨fun A => (σ.1 A).left, fun A B => by
    have h := congrArg SemidirectProduct.left (σ.1.map_mul A B)
    rw [SemidirectProduct.mul_left, σ.2 A] at h
    exact h⟩
  left_inv _ := rfl
  right_inv σ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro A
    apply SemidirectProduct.ext
    · rfl
    · exact (σ.2 A).symm

/-- The section attached to a cocycle is `A ↦ (z(A), A)`
(paper `sec:normalization`, cocycle paragraph). -/
@[simp]
theorem cocycleSectionEquiv_apply (z : Cocycle θ) (A : H) :
    (cocycleSectionEquiv θ z).1 A = ⟨z.1 A, A⟩ := rfl

/-- The cocycle attached to a section `σ` is `A ↦ (σ A).left`
(paper `sec:normalization`, cocycle paragraph). -/
@[simp]
theorem cocycleSectionEquiv_symm_apply (σ : SemidirectSection θ) (A : H) :
    ((cocycleSectionEquiv θ).symm σ).1 A = (σ.1 A).left := rfl

/-- The trivial cocycle corresponds to the canonical section `inr`
(paper `sec:normalization`, cocycle paragraph). -/
theorem cocycleSectionEquiv_one :
    cocycleSectionEquiv θ ⟨fun _ => 1, isCocycle_one θ⟩ = ⟨inr, fun _ => rfl⟩ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro A
  rfl

/-! ### Conjugation by the kernel -/

/-- Conjugation by `(c, 1) = inl c` in `G ⋊[θ] H`: `(c,1)(g,A)(c,1)⁻¹ = (c g θ_A(c⁻¹), A)`
(paper `sec:normalization`, cocycle paragraph). -/
theorem conj_inl_mk (c g : G) (A : H) :
    (inl c * ⟨g, A⟩ * (inl c)⁻¹ : G ⋊[θ] H) = ⟨c * g * θ A c⁻¹, A⟩ := by
  ext <;> simp

/-- Conjugating the section value `(z(A), A)` by `(c, 1)` gives `(c z(A) θ_A(c⁻¹), A)`
(paper `sec:normalization`, cocycle paragraph). -/
theorem conj_inl_section (z : H → G) (c : G) (A : H) :
    (inl c * ⟨z A, A⟩ * (inl c)⁻¹ : G ⋊[θ] H) = ⟨c * z A * θ A c⁻¹, A⟩ :=
  conj_inl_mk θ c (z A) A

/-! ### Cohomology relation and `H¹` -/

/-- `z` and `z'` are cohomologous: `z'(A) = c z(A) θ_A(c⁻¹)` for some `c : G`
(paper `sec:normalization`, cocycle paragraph). -/
def Cohomologous (z z' : H → G) : Prop := ∃ c : G, ∀ A : H, z' A = c * z A * θ A c⁻¹

/-- Reflexivity of `Cohomologous` (paper `sec:normalization`, cocycle paragraph). -/
theorem Cohomologous.refl (z : H → G) : Cohomologous θ z z :=
  ⟨1, fun A => by simp⟩

variable {θ} in
/-- Symmetry of `Cohomologous` (paper `sec:normalization`, cocycle paragraph). -/
theorem Cohomologous.symm {z z' : H → G} (h : Cohomologous θ z z') : Cohomologous θ z' z := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c⁻¹, fun A => ?_⟩
  rw [hc A]
  simp only [map_inv, inv_inv]
  group

variable {θ} in
/-- Transitivity of `Cohomologous` (paper `sec:normalization`, cocycle paragraph). -/
theorem Cohomologous.trans {z z' z'' : H → G} (h : Cohomologous θ z z')
    (h' : Cohomologous θ z' z'') : Cohomologous θ z z'' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := h'
  refine ⟨d * c, fun A => ?_⟩
  rw [hd A, hc A]
  simp only [map_inv, map_mul, mul_inv_rev]
  group

/-- `Cohomologous θ` is an equivalence relation (paper `sec:normalization`, cocycle paragraph). -/
theorem cohomologous_equivalence : Equivalence (Cohomologous θ) :=
  ⟨Cohomologous.refl θ, Cohomologous.symm, Cohomologous.trans⟩

variable {θ} in
/-- Being a cocycle is invariant under the cohomology relation
(paper `sec:normalization`, cocycle paragraph). -/
theorem IsCocycle.of_cohomologous {z z' : H → G} (hz : IsCocycle θ z)
    (h : Cohomologous θ z z') : IsCocycle θ z' := by
  obtain ⟨c, hc⟩ := h
  intro A B
  rw [hc (A * B), hc A, hc B, hz A B]
  simp only [map_mul, MulAut.mul_apply, map_inv]
  group

/-- The cohomology relation as a setoid on cocycles
(paper `sec:normalization`, cocycle paragraph). -/
def cohomologousSetoid : Setoid (Cocycle θ) where
  r z z' := Cohomologous θ z.1 z'.1
  iseqv := ⟨fun z => Cohomologous.refl θ z.1, fun h => h.symm, fun h h' => h.trans h'⟩

/-- Nonabelian first cohomology `H¹(H,G)` for `θ : H →* MulAut G`: cocycles modulo
`z'(A) = c z(A) θ_A(c⁻¹)` (paper `sec:normalization`, cocycle paragraph).

For nonabelian `G` this is only a **pointed set** (basepoint `H1.trivialClass`). It classifies
sections of the fixed split extension `G ⋊[θ] H`, equivalently complements of the kernel, up to
conjugation by `G` (`H1EquivSectionClasses`, `H1EquivComplementClasses`); it does **not**
classify extensions. -/
def H1 : Type _ := Quotient (cohomologousSetoid θ)

/-- The class of a cocycle in `H¹(H,G)` (paper `sec:normalization`, cocycle paragraph). -/
def H1.mk (z : Cocycle θ) : H1 θ := Quotient.mk (cohomologousSetoid θ) z

/-- The distinguished basepoint of the pointed set `H¹(H,G)`: the class of the trivial cocycle
(paper `sec:normalization`, cocycle paragraph). -/
def H1.trivialClass : H1 θ := H1.mk θ ⟨fun _ => 1, isCocycle_one θ⟩

/-- `H¹(H,G)` is inhabited by its basepoint (paper `sec:normalization`, cocycle paragraph). -/
instance : Inhabited (H1 θ) := ⟨H1.trivialClass θ⟩

/-- `H¹(H,G)` as an object of the category of pointed types
(paper `sec:normalization`, cocycle paragraph). -/
def H1.toPointed : Pointed := ⟨H1 θ, H1.trivialClass θ⟩

/-- Every cohomology class is the class of a cocycle
(paper `sec:normalization`, cocycle paragraph). -/
theorem H1.mk_surjective : Function.Surjective (H1.mk θ) :=
  Quotient.mk_surjective

/-- Two cocycles have the same class iff they are cohomologous
(paper `sec:normalization`, cocycle paragraph). -/
theorem H1.mk_eq_mk_iff (z z' : Cocycle θ) :
    H1.mk θ z = H1.mk θ z' ↔ Cohomologous θ z.1 z'.1 :=
  Quotient.eq (r := cohomologousSetoid θ)

/-- The coboundary `z_c` is cohomologous to the trivial cocycle
(paper `sec:normalization`, cocycle paragraph). -/
theorem cohomologous_one_coboundary (c : G) :
    Cohomologous θ (fun _ => 1) (coboundary θ c) :=
  ⟨c, fun A => by simp [coboundary]⟩

/-- The coboundary `z_c` represents the distinguished trivial class of `H¹(H,G)`
(paper `sec:normalization`, cocycle paragraph). -/
theorem H1.mk_coboundary (c : G) :
    H1.mk θ ⟨coboundary θ c, isCocycle_coboundary θ c⟩ = H1.trivialClass θ :=
  ((H1.mk_eq_mk_iff θ _ _).2 (cohomologous_one_coboundary θ c)).symm

/-- A cocycle represents the trivial class iff it is a coboundary
(paper `sec:normalization`, cocycle paragraph). -/
theorem H1.mk_eq_trivialClass_iff (z : Cocycle θ) :
    H1.mk θ z = H1.trivialClass θ ↔ ∃ c : G, z.1 = coboundary θ c := by
  unfold H1.trivialClass
  rw [H1.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c⁻¹, funext fun A => ?_⟩
    have h : (1 : G) = c * z.1 A * θ A c⁻¹ := hc A
    simp only [coboundary, inv_inv]
    calc z.1 A = c⁻¹ * (c * z.1 A * θ A c⁻¹) * (θ A c⁻¹)⁻¹ := by group
      _ = c⁻¹ * 1 * (θ A c⁻¹)⁻¹ := by rw [← h]
      _ = c⁻¹ * θ A c := by simp
  · rintro ⟨c, hc⟩
    refine ⟨c⁻¹, fun A => ?_⟩
    show (1 : G) = c⁻¹ * z.1 A * θ A c⁻¹⁻¹
    rw [hc]
    simp [coboundary]

/-! ### Sections up to conjugation by the kernel -/

/-- Two sections are conjugate by the kernel: `σ' A = (c,1) σ(A) (c,1)⁻¹` for one `c : G` and all
`A` (paper `sec:normalization`, cocycle paragraph). -/
def SectionConj (σ σ' : SemidirectSection θ) : Prop :=
  ∃ c : G, ∀ A : H, σ'.1 A = inl c * σ.1 A * (inl c)⁻¹

/-- `SectionConj` is conjugation by an element of the kernel `rightHom.ker = inl.range`
(paper `sec:normalization`, cocycle paragraph). -/
theorem sectionConj_iff_exists_ker (σ σ' : SemidirectSection θ) :
    SectionConj θ σ σ' ↔
      ∃ k ∈ (rightHom : G ⋊[θ] H →* H).ker, ∀ A : H, σ'.1 A = k * σ.1 A * k⁻¹ := by
  rw [← range_inl_eq_ker_rightHom]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨inl c, ⟨c, rfl⟩, hc⟩
  · rintro ⟨_, ⟨c, rfl⟩, hk⟩
    exact ⟨c, hk⟩

/-- The cohomology relation on cocycles is precisely conjugation by `(c, 1)` of the associated
sections (paper `sec:normalization`, cocycle paragraph). -/
theorem cohomologous_iff_sectionConj (z z' : Cocycle θ) :
    Cohomologous θ z.1 z'.1 ↔
      SectionConj θ (cocycleSectionEquiv θ z) (cocycleSectionEquiv θ z') := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun A => ?_⟩
    rw [cocycleSectionEquiv_apply, cocycleSectionEquiv_apply, conj_inl_section, hc A]
  · rintro ⟨c, hc⟩
    refine ⟨c, fun A => ?_⟩
    have h := hc A
    rw [cocycleSectionEquiv_apply, cocycleSectionEquiv_apply, conj_inl_section] at h
    exact congrArg SemidirectProduct.left h

/-- Conjugation of sections by the kernel, as a setoid; it is an equivalence relation because it
corresponds to `Cohomologous` (paper `sec:normalization`, cocycle paragraph). -/
def sectionConjSetoid : Setoid (SemidirectSection θ) where
  r := SectionConj θ
  iseqv := by
    have key : ∀ σ σ' : SemidirectSection θ, SectionConj θ σ σ' ↔
        Cohomologous θ ((cocycleSectionEquiv θ).symm σ).1 ((cocycleSectionEquiv θ).symm σ').1 := by
      intro σ σ'
      rw [cohomologous_iff_sectionConj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine ⟨fun σ => (key σ σ).2 (Cohomologous.refl θ _), fun h => ?_, fun h h' => ?_⟩
    · exact (key _ _).2 ((key _ _).1 h).symm
    · exact (key _ _).2 (((key _ _).1 h).trans ((key _ _).1 h'))

/-- `H¹(H,G)` is in bijection with sections of the fixed split extension `G ⋊[θ] H` modulo
conjugation by the kernel `G` (paper `sec:normalization`, cocycle paragraph). This is a
bijection of pointed sets classifying sections up to `G`-conjugacy, not extensions. -/
def H1EquivSectionClasses : H1 θ ≃ Quotient (sectionConjSetoid θ) :=
  Quotient.congr (cocycleSectionEquiv θ) (cohomologous_iff_sectionConj θ)

/-- `H1EquivSectionClasses` sends the class of a cocycle to the class of its section
(paper `sec:normalization`, cocycle paragraph). -/
theorem H1EquivSectionClasses_mk (z : Cocycle θ) :
    H1EquivSectionClasses θ (H1.mk θ z) =
      Quotient.mk (sectionConjSetoid θ) (cocycleSectionEquiv θ z) := rfl

/-- `H1EquivSectionClasses` preserves basepoints: the trivial class goes to the class of the
canonical section `inr` (paper `sec:normalization`, cocycle paragraph). -/
theorem H1EquivSectionClasses_trivialClass :
    H1EquivSectionClasses θ (H1.trivialClass θ) =
      Quotient.mk (sectionConjSetoid θ) ⟨inr, fun _ => rfl⟩ := by
  rw [H1.trivialClass, H1EquivSectionClasses_mk, cocycleSectionEquiv_one]

/-! ### Complements of the kernel -/

/-- The image of a section is a complement of the kernel `inl.range = rightHom.ker`
(paper `sec:normalization`, cocycle paragraph). -/
theorem section_range_isComplement (σ : SemidirectSection θ) :
    Subgroup.IsComplement' (inl : G →* G ⋊[θ] H).range σ.1.range := by
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique]
  intro x
  refine ⟨(⟨inl (x.left * (σ.1 x.right).left⁻¹), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩,
    ⟨σ.1 x.right, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩), ?_, ?_⟩
  · ext
    · simp
    · simp [σ.2 x.right]
  · rintro ⟨⟨_, c, rfl⟩, ⟨_, A, rfl⟩⟩ rfl
    have hA : (inl c * σ.1 A).right = A := by simp [σ.2 A]
    ext : 1
    · apply Subtype.ext
      simp [hA]
    · apply Subtype.ext
      simp [hA]

/-- The type of complements of the kernel `inl.range` in the fixed extension `G ⋊[θ] H`
(paper `sec:normalization`, cocycle paragraph). -/
abbrev KernelComplement :=
  {K : Subgroup (G ⋊[θ] H) // Subgroup.IsComplement' (inl : G →* G ⋊[θ] H).range K}

/-- A complement of the kernel contains exactly one element over each `A : H`
(paper `sec:normalization`, cocycle paragraph). -/
theorem KernelComplement.existsUnique (K : KernelComplement θ) (A : H) :
    ∃! k : G ⋊[θ] H, k ∈ K.1 ∧ k.right = A := by
  obtain ⟨⟨⟨n, hn⟩, ⟨k, hk⟩⟩, hnk, -⟩ := K.2.existsUnique (inr A)
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hn
  refine ⟨k, ⟨hk, ?_⟩, ?_⟩
  · have h := congrArg SemidirectProduct.right hnk
    simpa using h
  · rintro k' ⟨hk', hr'⟩
    have hmem : k' * k⁻¹ ∈ K.1 := K.1.mul_mem hk' (K.1.inv_mem hk)
    have hr : (k' * k⁻¹).right = 1 := by
      have h := congrArg SemidirectProduct.right hnk
      simp only [SemidirectProduct.mul_right, right_inl, one_mul, right_inr] at h
      simp [hr', h]
    have hker : k' * k⁻¹ ∈ (inl : G →* G ⋊[θ] H).range := by
      refine MonoidHom.mem_range.2 ⟨(k' * k⁻¹).left, ?_⟩
      conv_rhs => rw [← inl_left_mul_inr_right (k' * k⁻¹)]
      rw [hr, map_one, mul_one]
    have h1 := Subgroup.disjoint_def.1 K.2.disjoint hker hmem
    exact mul_inv_eq_one.1 h1

/-- The unique element of a complement `K` lying over `A : H`
(paper `sec:normalization`, cocycle paragraph). -/
noncomputable def complementElt (K : KernelComplement θ) (A : H) : G ⋊[θ] H :=
  (KernelComplement.existsUnique θ K A).exists.choose

/-- `complementElt K A ∈ K` (paper `sec:normalization`, cocycle paragraph). -/
theorem complementElt_mem (K : KernelComplement θ) (A : H) : complementElt θ K A ∈ K.1 :=
  (KernelComplement.existsUnique θ K A).exists.choose_spec.1

/-- `complementElt K A` lies over `A` (paper `sec:normalization`, cocycle paragraph). -/
theorem complementElt_right (K : KernelComplement θ) (A : H) : (complementElt θ K A).right = A :=
  (KernelComplement.existsUnique θ K A).exists.choose_spec.2

/-- Uniqueness of the element of a complement over `A`
(paper `sec:normalization`, cocycle paragraph). -/
theorem eq_complementElt (K : KernelComplement θ) {A : H} {k : G ⋊[θ] H} (hk : k ∈ K.1)
    (hr : k.right = A) : k = complementElt θ K A :=
  (KernelComplement.existsUnique θ K A).unique ⟨hk, hr⟩
    ⟨complementElt_mem θ K A, complementElt_right θ K A⟩

/-- The section `A ↦ complementElt K A` determined by a complement of the kernel
(paper `sec:normalization`, cocycle paragraph). -/
noncomputable def complementSection (K : KernelComplement θ) : SemidirectSection θ :=
  ⟨{ toFun := complementElt θ K
     map_one' := (eq_complementElt θ K K.1.one_mem rfl).symm
     map_mul' := fun A B =>
       (eq_complementElt θ K (K.1.mul_mem (complementElt_mem θ K A) (complementElt_mem θ K B))
         (by simp [complementElt_right])).symm },
    complementElt_right θ K⟩

/-- Sections of `rightHom` correspond bijectively to complements of the kernel, via `σ ↦ σ.range`
(paper `sec:normalization`, cocycle paragraph). -/
noncomputable def sectionComplementEquiv : SemidirectSection θ ≃ KernelComplement θ where
  toFun σ := ⟨σ.1.range, section_range_isComplement θ σ⟩
  invFun K := complementSection θ K
  left_inv σ := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro A
    exact (eq_complementElt θ ⟨σ.1.range, section_range_isComplement θ σ⟩
      (MonoidHom.mem_range.2 ⟨A, rfl⟩) (σ.2 A)).symm
  right_inv K := by
    apply Subtype.ext
    apply le_antisymm
    · rintro _ ⟨A, rfl⟩
      exact complementElt_mem θ K A
    · intro k hk
      exact MonoidHom.mem_range.2 ⟨k.right, (eq_complementElt θ K hk rfl).symm⟩

/-- `sectionComplementEquiv` sends a section to its image
(paper `sec:normalization`, cocycle paragraph). -/
@[simp]
theorem sectionComplementEquiv_apply (σ : SemidirectSection θ) :
    (sectionComplementEquiv θ σ).1 = σ.1.range := rfl

/-- Two complements of the kernel are conjugate by the kernel: `K' = (c,1) K (c,1)⁻¹`
(paper `sec:normalization`, cocycle paragraph). -/
def ComplementConj (K K' : KernelComplement θ) : Prop :=
  ∃ c : G, K'.1 = K.1.map (MulAut.conj (inl c : G ⋊[θ] H)).toMonoidHom

/-- Sections are conjugate by the kernel iff their images are
(paper `sec:normalization`, cocycle paragraph). -/
theorem sectionConj_iff_complementConj (σ σ' : SemidirectSection θ) :
    SectionConj θ σ σ' ↔
      ComplementConj θ (sectionComplementEquiv θ σ) (sectionComplementEquiv θ σ') := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hσ : σ'.1 = (MulAut.conj (inl c : G ⋊[θ] H)).toMonoidHom.comp σ.1 := by
      apply MonoidHom.ext
      intro A
      simp [hc A, MulAut.conj_apply]
    rw [sectionComplementEquiv_apply, sectionComplementEquiv_apply, hσ, MonoidHom.range_comp]
  · rintro ⟨c, hK⟩
    refine ⟨c, fun A => ?_⟩
    have hmem : inl c * σ.1 A * (inl c)⁻¹ ∈ (sectionComplementEquiv θ σ').1 := by
      rw [hK, Subgroup.mem_map]
      exact ⟨σ.1 A, MonoidHom.mem_range.2 ⟨A, rfl⟩, by simp [MulAut.conj_apply]⟩
    have hr : (inl c * σ.1 A * (inl c)⁻¹ : G ⋊[θ] H).right = A := by
      simp [σ.2 A]
    rw [eq_complementElt θ (sectionComplementEquiv θ σ') hmem hr]
    exact eq_complementElt θ (sectionComplementEquiv θ σ') (MonoidHom.mem_range.2 ⟨A, rfl⟩) (σ'.2 A)

/-- Conjugacy of complements by the kernel, as a setoid
(paper `sec:normalization`, cocycle paragraph). -/
def complementConjSetoid : Setoid (KernelComplement θ) where
  r := ComplementConj θ
  iseqv := by
    have key : ∀ K K' : KernelComplement θ, ComplementConj θ K K' ↔
        SectionConj θ ((sectionComplementEquiv θ).symm K) ((sectionComplementEquiv θ).symm K') := by
      intro K K'
      rw [sectionConj_iff_complementConj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have e := (sectionConjSetoid θ).iseqv
    refine ⟨fun K => (key K K).2 (e.refl _), fun h => ?_, fun h h' => ?_⟩
    · exact (key _ _).2 (e.symm ((key _ _).1 h))
    · exact (key _ _).2 (e.trans ((key _ _).1 h) ((key _ _).1 h'))

/-- `H¹(H,G)` classifies complements of the kernel `G` in the fixed split extension `G ⋊[θ] H` up
to conjugation by `G` (paper `sec:normalization`, cocycle paragraph). A bijection of pointed
sets (basepoints: `H1.trivialClass` and the class of the canonical complement `inr.range`, see
`H1EquivComplementClasses_trivialClass`); it does not classify extensions. -/
noncomputable def H1EquivComplementClasses : H1 θ ≃ Quotient (complementConjSetoid θ) :=
  (H1EquivSectionClasses θ).trans
    (Quotient.congr (sectionComplementEquiv θ) (sectionConj_iff_complementConj θ))

/-- `H1EquivComplementClasses` sends the class of `z` to the class of the complement
`{(z(A), A)}` (paper `sec:normalization`, cocycle paragraph). -/
theorem H1EquivComplementClasses_mk (z : Cocycle θ) :
    H1EquivComplementClasses θ (H1.mk θ z) =
      Quotient.mk (complementConjSetoid θ)
        (sectionComplementEquiv θ (cocycleSectionEquiv θ z)) := rfl

/-- `H1EquivComplementClasses` preserves basepoints: the trivial class goes to the class of the
canonical complement `(inr : H →* G ⋊[θ] H).range` (paper `sec:normalization`, cocycle
paragraph). -/
theorem H1EquivComplementClasses_trivialClass :
    H1EquivComplementClasses θ (H1.trivialClass θ) =
      Quotient.mk (complementConjSetoid θ)
        ⟨(inr : H →* G ⋊[θ] H).range, section_range_isComplement θ ⟨inr, fun _ => rfl⟩⟩ := by
  rw [H1.trivialClass, H1EquivComplementClasses_mk, cocycleSectionEquiv_one]
  rfl

end OECocycle
