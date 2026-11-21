import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationPreservesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBoundStatement

section
section
open NumberField

namespace GlobalTheory

theorem eOp_comp_self_of_conv_idem {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL)
    (he : ∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) : A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc
  have hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL)
      = (((A.chi k)⁻¹ : LLˣ) : LL) := by
    intro g k
    rw [← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]
  have hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k := by
    intro k
    calc ∑ g, c g * c (g⁻¹ * k)
        = ∑ g, (eC g * eC (g⁻¹ * k)) * (((A.chi k)⁻¹ : LLˣ) : LL) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hc, ← hchi g k]; ring
      _ = c k := by rw [← Finset.sum_mul, he k]
  have hE : A.eOp eC = ∑ g, c g • A.ρ g := rfl
  rw [← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]
  calc ∑ g, ∑ h, (c g • A.ρ g) * (c h • A.ρ h)
      = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • A.ρ k := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, c k • A.ρ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcc k]

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) → A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  atlas_forward_decl GlobalTheory.eOp_comp_self_of_conv_idem
end

section
section
open NumberField

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory

theorem twistedProjector_orthogonal_of_unitary : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC σ hid hu hc x y
  have hunit : ∀ g : G0, starRingEnd ℂ (σ ((A.chi g : LLˣ) : LL)) = (σ ((A.chi g : LLˣ) : LL))⁻¹ := by
    intro g
    set z := σ ((A.chi g : LLˣ) : LL)
    have hpow : z ^ orderOf g = 1 := by
      have h1 : A.chi g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 : ((A.chi g : LLˣ) : LL) ^ orderOf g = 1 := by
        rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simp only [z]; rw [← map_pow, h2, map_one]
    have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos g).ne'
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hm : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact eq_inv_of_mul_eq_one_right hm
  have key : ∀ g u v, ⟪A.j σ (A.ρ g u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.ρ g⁻¹ v)⟫_ℂ := by
    intro g u v
    have h1 : A.ρ g (A.ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hu g u (A.ρ g⁻¹ v), h1]
  have sa : ∀ u v, ⟪A.j σ (A.eOp eC u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.eOp eC v)⟫_ℂ := by
    intro u v
    simp only [Formalism.IndefR.Arith.FormsL.eOp_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.inv G0)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [key g, Equiv.inv_apply]
    congr 1
    rw [map_mul, map_mul, map_mul, hc, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      map_inv₀, map_inv₀, map_inv₀, hunit]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  have horth : ⟪A.j σ (A.eOp eC x), A.j σ (y - A.eOp eC y)⟫_ℂ = 0 := by
    have hy : A.eOp eC (A.eOp eC y) = A.eOp eC y := LinearMap.congr_fun hid y
    rw [sa, map_sub, hy, sub_self, map_zero, inner_zero_right]
  rw [map_add]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  simpa only [sq] using h

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.twistedProjector_orthogonal_of_unitary
end

section
section
open NumberField

namespace GlobalTheory

open Formalism.IndefR.Arith

theorem card_smul_eOp_mem_Mall : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ g h, eC (h * g * h⁻¹) = eC g) → (∀ g, IsIntegral ℤ ((Fintype.card G0 : LL) * eC g)) →
    (∀ g f, f ∈ A.MK → A.ρ g f ∈ A.MK) → ∀ (J0 : Subgroup G0) (lam0 : J0 →* LLˣ),
    ∀ x ∈ A.Mall J0 lam0, ((Fintype.card G0 : ℕ) : LL) • A.eOp eC x ∈ A.Mall J0 lam0 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC hcl hint hMK J0 lam0 x hx
  classical
  rw [FormsL.Mall, Submodule.mem_inf] at hx ⊢
  have hρspan : ∀ g, ∀ y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      A.ρ g y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (hMK g z hz)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
        rw [← algebraMap_smul LL r a, LinearMap.map_smul, algebraMap_smul]
        exact Submodule.smul_mem _ r ha
  have hchi : ∀ g, IsIntegral ℤ (((A.chi g)⁻¹ : LLˣ) : LL) := by
    intro g
    have h1 : ((A.chi g)⁻¹) ^ (orderOf g) = 1 := by
      rw [← map_inv, ← map_pow, inv_pow, pow_orderOf_eq_one, inv_one, map_one]
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact isIntegral_one
  have hchic : ∀ p g : G0, A.chi (p * g * p⁻¹) = A.chi g := by
    intro p g
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  constructor
  · rw [FormsL.eOp_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [smul_smul]
    have hi : IsIntegral ℤ (((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ))) := by
      rw [← mul_assoc]; exact (hint g).mul (hchi g)
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 LL, algebraMap (𝓞 LL) LL r =
        ((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ)) := ⟨⟨_, hi⟩, rfl⟩
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (hρspan g x hx.1)
  · have hcomm : ∀ p : G0, A.ρ p (A.eOp eC x) = A.eOp eC (A.ρ p x) := by
      intro p
      rw [FormsL.eOp_apply, FormsL.eOp_apply, map_sum]
      simp only [LinearMap.map_smul]
      refine Fintype.sum_equiv (MulAut.conj p).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcl g p, hchic p g, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]
    intro p
    show A.ρ p (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x) =
      ((A.chi p * lam0 p : LLˣ) : LL) • (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x)
    rw [LinearMap.map_smul, hcomm, hx.2 p, LinearMap.map_smul, smul_comm]

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_smul_twistedProjector_mem_integralForms : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ g h, eC (h * g * h⁻¹) = eC g) → (∀ g, IsIntegral ℤ ((Fintype.card G0 : LL) * eC g)) →
    (∀ g f, f ∈ A.MK → A.ρ g f ∈ A.MK) → ∀ (J0 : Subgroup G0) (lam0 : J0 →* LLˣ),
    ∀ x ∈ A.Mall J0 lam0, ((Fintype.card G0 : ℕ) : LL) • A.eOp eC x ∈ A.Mall J0 lam0 := by
  atlas_forward_decl GlobalTheory.card_smul_eOp_mem_Mall
end

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_rows {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.Rows) (ht : RecTied D L) (i : Fin D.R.m) (PP A : ℝ) (hN : HostNum D L PP A 3) : CutAt p i := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.group_idempotent_coefficients p hp ht
  have hI := GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h1
  refine ⟨hI, fun σ x y => ?_, fun x hx => ?_, GlobalTheory.T.log_group_order_bound p hp ht PP A hN⟩
  · exact GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) _ hI (GlobalTheory.T.row_inner_product_invariant p hp ht i σ)
      (fun g => h4 _ g) x y
  · exact GlobalTheory.T.card_smul_twistedProjector_mem_integralForms (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h2 h3 (GlobalTheory.T.row_representation_preserves_lattice p hp ht i) _ _ x hx

theorem cut_of_hypotheses (_h : Hypotheses2) : Cut := by
  refine (Sizes.hostN 3).imp fun Fm CH _ h => ?_
  obtain ⟨C, -, x0, hx⟩ := h
  exact ⟨0, le_rfl, x0, fun x hx' hle ι p hp i => cutAt_of_rows p hp.1 hp.2 i _ _ (hx x hx' hle ι p hp i)⟩

end GlobalTheory.CovTop
end
end
