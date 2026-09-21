import ObserverEquivariance.BaseChange
import ObserverEquivariance.Cocycles

/-!
# Changing parallel normalization and the class in `H¹(H,G)` (paper `sec:normalization`)

Bridge between `BaseChange` (the datum-level `prop:basechange`) and `Cocycles` (pure nonabelian
group cohomology of the fixed split extension `G ⋊_θ H`).

Paper labels covered (paragraph after `prop:basechange` and the cocycle paragraph of
`sec:normalization`):

* `baseChange_twistFactor_eq_coboundary`: the factor `z_c(A) = c θ_A(c⁻¹)` of `prop:basechange`
  is `OECocycle.coboundary θ c A`, so its cocycle identity is `OECocycle.coboundary_mul`;
* `liftHomθOver_rebase_conj_ker`: "The conjugacy class of the canonical section under the kernel
  is independent of parallel normalization" — the new canonical section, transported back along
  `autBoxGθOverCongr`, is conjugate to the old one by ONE element of `(ΦθOver d H θ).ker`,
  uniformly in `A` (namely `Λ_c`);
* `liftHomθOver_rebase_semidirect`: read in the FIXED semidirect coordinates
  `autBoxGθOverMulEquivSemidirect d` of the old normalization, the new canonical section is the
  cocycle section `A ↦ (z_c(A), A)` of the coboundary `z_c` (with `c`, not `c⁻¹`);
* `liftHomθOver_rebase_sectionConj`: in those coordinates it is conjugate to the old canonical
  section `inr` by `(c, 1)`;
* `liftHomθOver_rebase_class`: its class in `H¹(H,G)` (via `OECocycle.H1EquivSectionClasses`) is
  the distinguished trivial class, i.e. "changing parallel normalization conjugates the canonical
  section without changing its class in `H¹(H,G)`".  The extension `G ⋊_θ H` itself is fixed
  throughout (it is the target of `autBoxGθOverMulEquivSemidirect d`), so the underlying extension
  does not change either.

As in `BaseChange`, `hact`/`hreind` fix the right action and the transport, and
`hc : ∀ s, d'.base s = d.act (d.base s) c` records the change of parallel basepoints.
-/

open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G] {p : O ⥤ S}

/-- The factor `z_c(A) = c θ_A(c⁻¹)` of `prop:basechange` is the nonabelian `1`-coboundary
    `OECocycle.coboundary θ c A` (paper `sec:normalization`, cocycle paragraph); hence
    `baseChange_twistFactor_mul` is `OECocycle.coboundary_mul`. -/
theorem baseChange_twistFactor_eq_coboundary {H : Type*} [Group H] (θ : H →* MulAut G) (c : G)
    (A : H) : c * θ A c⁻¹ = OECocycle.coboundary θ c A := rfl

section Rebase

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy)
  {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c)
  (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)

include hact hc in
/-- Kernel conjugacy (paper, paragraph after `prop:basechange`: "The conjugacy class of the
    canonical section under the kernel is independent of parallel normalization"): the new
    canonical twisted section, transported back along `autBoxGθOverCongr`, is conjugate to the
    old one by a single element `k` of the kernel of `ΦθOver d H θ`, uniformly in `A`. -/
theorem liftHomθOver_rebase_conj_ker :
    ∃ k ∈ (ΦθOver d H θ).ker, ∀ A : H,
      (autBoxGθOverCongr d d' hact hreind H θ).symm (liftHomθOver d' H θ A)
        = k * liftHomθOver d H θ A * k⁻¹ :=
  ⟨ΛHomθOver d H θ c, ΛHomθOver_base d H θ c, fun A => by
    rw [liftHomθOver_eq_conj_of_base d d' hact hreind hc, MulEquiv.symm_apply_apply,
      MulAut.conj_apply]⟩

variable [IsConnected S]

include hc in
/-- The new canonical section in the old semidirect coordinates (paper `sec:normalization`,
    cocycle paragraph): `ψ_d((autBoxGθOverCongr)⁻¹ Ã'_θ) = (z_c(A), A)`, the cocycle section of
    the coboundary `z_c(A) = c θ_A(c⁻¹)`, where `ψ_d = autBoxGθOverMulEquivSemidirect d H θ`. -/
theorem liftHomθOver_rebase_semidirect (A : H) :
    autBoxGθOverMulEquivSemidirect d H θ
        ((autBoxGθOverCongr d d' hact hreind H θ).symm (liftHomθOver d' H θ A))
      = OECocycle.cocycleSection (OECocycle.isCocycle_coboundary θ c) A := by
  rw [liftHomθOver_eq_of_base d d' hact hreind hc, MulEquiv.symm_apply_apply,
    MulEquiv.apply_eq_iff_symm_apply]
  show _ = semidirectToAutBoxGθOver d H θ ⟨c * θ A c⁻¹, A⟩
  have h := (semidirectToAutBoxGθOver d H θ).map_mul (SemidirectProduct.inl (c * θ A c⁻¹))
    (SemidirectProduct.inr A)
  rw [semidirectToAutBoxGθOver_inl, semidirectToAutBoxGθOver_inr] at h
  have hx : (⟨c * θ A c⁻¹, A⟩ : SemidirectProduct G H θ)
      = SemidirectProduct.inl (c * θ A c⁻¹) * SemidirectProduct.inr A := by ext <;> simp
  rw [hx, h]

/-- The new canonical twisted section `Ã'_θ`, read in the fixed semidirect coordinates of the
    old normalization, as a section of `rightHom : G ⋊_θ H →* H` (paper `sec:normalization`,
    paragraph after `prop:basechange`): `A ↦ ψ_d((autBoxGθOverCongr)⁻¹ Ã'_θ)`. -/
noncomputable def liftHomθOverRebaseSection : OECocycle.SemidirectSection θ :=
  ⟨(autBoxGθOverMulEquivSemidirect d H θ).toMonoidHom.comp
      ((autBoxGθOverCongr d d' hact hreind H θ).symm.toMonoidHom.comp (liftHomθOver d' H θ)),
    fun A => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        autBoxGθOverMulEquivSemidirect_apply_right]
      rfl⟩

include hc in
/-- Changing parallel normalization conjugates the canonical section by the kernel (paper
    `sec:normalization`): in the fixed semidirect coordinates of `d`, the new section is
    conjugate to the old canonical section `inr` by `(c, 1)`. -/
theorem liftHomθOver_rebase_sectionConj :
    OECocycle.SectionConj θ ⟨SemidirectProduct.inr, fun _ => rfl⟩
      (liftHomθOverRebaseSection d d' hact hreind H θ) :=
  ⟨c, fun A => by
    change autBoxGθOverMulEquivSemidirect d H θ
        ((autBoxGθOverCongr d d' hact hreind H θ).symm (liftHomθOver d' H θ A)) = _
    rw [liftHomθOver_rebase_semidirect d d' hact hreind hc H θ A]
    have h := OECocycle.conj_inl_section θ (fun _ : H => (1 : G)) c A
    rw [mul_one] at h
    exact h.symm⟩

include hc in
/-- Changing parallel normalization does not change the class in `H¹(H,G)` (paper
    `sec:normalization`, cocycle paragraph: "conjugates the canonical section without changing
    its class in `H¹(H,G)`"): the class of the new section under conjugation by the kernel is
    the image of the distinguished trivial class under `OECocycle.H1EquivSectionClasses`. -/
theorem liftHomθOver_rebase_class :
    Quotient.mk (OECocycle.sectionConjSetoid θ) (liftHomθOverRebaseSection d d' hact hreind H θ)
      = OECocycle.H1EquivSectionClasses θ (OECocycle.H1.trivialClass θ) := by
  rw [OECocycle.H1EquivSectionClasses_trivialClass]
  exact (Quotient.sound (liftHomθOver_rebase_sectionConj d d' hact hreind hc H θ)).symm

end Rebase
