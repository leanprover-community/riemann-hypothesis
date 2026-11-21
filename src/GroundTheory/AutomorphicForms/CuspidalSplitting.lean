import Mathlib
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.AutomorphicForms.LeviStagesProduct
import GroundTheory.AutomorphicForms.LeviStagesExact

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

section Sums

variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]

def quotSum (Φ : G → M) : M :=
  ∑ᶠ q : G ⧸ H, Φ q.out

variable {H}

theorem quotSum_def (Φ : G → M) : quotSum H Φ = ∑ᶠ q : G ⧸ H, Φ q.out := rfl

theorem apply_out_mk {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hΦ g h h.2]

theorem quotSum_mul_left {Φ : G → M} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (x : G) :
    quotSum H (fun g => Φ (x * g)) = quotSum H Φ := by
  unfold quotSum
  calc ∑ᶠ q : G ⧸ H, Φ (x * q.out)
      = ∑ᶠ q : G ⧸ H, (fun q' : G ⧸ H => Φ q'.out) (MulAction.toPerm x q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm x q : G ⧸ H) = QuotientGroup.mk (x * q.out) := by
          rw [MulAction.toPerm_apply]
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        simp only [hq, apply_out_mk hΦ]
    _ = ∑ᶠ q : G ⧸ H, Φ q.out := finsum_comp_equiv (MulAction.toPerm x) (f := fun q' : G ⧸ H => Φ q'.out)

theorem quotSum_congr {Φ Ψ : G → M} (h : ∀ g, Φ g = Ψ g) : quotSum H Φ = quotSum H Ψ := by
  unfold quotSum
  exact finsum_congr fun q => h _

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quotSum (hH : IsOpen (H : Set G)) (hZH : Subgroup.center G ≤ H)
    {Φ : G → M} {C : Set G} (hC : IsCompact C)
    (hsupp : support Φ ⊆ (Subgroup.center G : Set G) * C) :
    (support fun q : G ⧸ H => Φ q.out).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine ((hC.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
  intro q hq
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp hq
  replace hzc : z * c = q.out := hzc
  refine ⟨c, hc, ?_⟩
  rw [← QuotientGroup.out_eq' q, ← hzc, QuotientGroup.eq]
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  rw [hzc', ← mul_assoc, inv_mul_cancel, one_mul]
  exact hZH hz

end Sums

section CompactModCenter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem IsCompactModCenter.mono {φ ψ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ)
    (h : support ψ ⊆ support φ) : IsCompactModCenter ψ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact ⟨C, hC, h.trans hsupp⟩

theorem IsCompactModCenter.comp_inv {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp (show g⁻¹ ∈ support φ from hg)
  replace hzc : z * c = g⁻¹ := hzc
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, by simpa using hc, ?_⟩
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  show z⁻¹ * c⁻¹ = g
  rw [← mul_inv_rev, ← hzc', hzc, inv_inv]

end CompactModCenter

end Parabolic

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

theorem linearMap_finsum {ι M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℂ M]
    [Module ℂ N] (L : M →ₗ[ℂ] N) {φ : ι → M} (h : HasFiniteSupport φ) :
    L (∑ᶠ i, φ i) = ∑ᶠ i, L (φ i) :=
  map_finsum L h

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section CentralChar

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

def HasCentralChar (ρ : Representation ℂ (GL (Fin n) F) U) (ω : GL (Fin n) F → ℂ) : Prop :=
  ∀ z ∈ Subgroup.center (GL (Fin n) F), ∀ u, ρ z u = ω z • u

variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem HasCentralChar.mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z z' : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (hz' : z' ∈ Subgroup.center (GL (Fin n) F)) : ω (z * z') = ω z * ω z' := by
  have h1 := h _ (mul_mem hz hz') u
  rw [map_mul, Module.End.mul_apply, h z' hz', map_smul, h z hz, smul_smul] at h1
  exact (smul_left_injective ℂ hu h1).symm.trans (mul_comm _ _)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem HasCentralChar.one (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0) : ω 1 = 1 := by
  have h1 : ω 1 • u = (1 : ℂ) • u := by
    rw [one_smul, ← h 1 (Subgroup.one_mem _) u, map_one, Module.End.one_apply]
  exact smul_left_injective ℂ hu h1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem HasCentralChar.inv_mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) : ω z⁻¹ * ω z = 1 := by
  rw [← h.mul hu (inv_mem hz) hz, inv_mul_cancel, h.one hu]

end CentralChar

section CenterSup

abbrev centerSup (K : Subgroup (GL (Fin n) F)) : Subgroup (GL (Fin n) F) :=
  Subgroup.center (GL (Fin n) F) ⊔ K

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_centerSup {K : Subgroup (GL (Fin n) F)} {x : GL (Fin n) F} :
    x ∈ centerSup K ↔ ∃ z ∈ Subgroup.center (GL (Fin n) F), ∃ k ∈ K, z * k = x :=
  Subgroup.mem_sup_of_normal_left

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem rightInv_centerSup {X : Type*} {K : Subgroup (GL (Fin n) F)} {Φ : GL (Fin n) F → X}
    (hZ : ∀ g, ∀ z ∈ Subgroup.center (GL (Fin n) F), Φ (g * z) = Φ g)
    (hK : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : ∀ g, ∀ h ∈ centerSup K, Φ (g * h) = Φ g := by
  intro g h hh
  obtain ⟨z, hz, k, hk, rfl⟩ := mem_centerSup.1 hh
  rw [← mul_assoc, hK _ k hk, hZ g z hz]

theorem isOpen_centerSup {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen (centerSup K : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono le_sup_right hKo

theorem finite_support_centerSup {M : Type*} [AddCommMonoid M] {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {Φ : GL (Fin n) F → M} {φ : GL (Fin n) F → ℂ}
    (hφ : IsCompactModCenter φ) (h : ∀ g, φ g = 0 → Φ g = 0) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => Φ q.out := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact finite_support_quotSum (isOpen_centerSup hKo) le_sup_left hC
    (fun g hg => hsupp (mt (h g) hg))

end CenterSup

section CoeffSum

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) F) V) (ρ : Representation ℂ (GL (Fin n) F) U)

def coeffSum (K : Subgroup (GL (Fin n) F)) (f : Module.Dual ℂ V) (u : U) (w : V) : U :=
  quotSum (centerSup K) fun g => f (π g⁻¹ w) • ρ g u

variable {π ρ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {u : U}
  {ω : GL (Fin n) F → ℂ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem coeffSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K) (w : V) :
    ∀ g, ∀ h ∈ centerSup K, f (π (g * h)⁻¹ w) • ρ (g * h) u = f (π g⁻¹ w) • ρ g u := by
  refine rightInv_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : π (g * z)⁻¹ w = ω z⁻¹ • π g⁻¹ w := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωπ _ (inv_mem hz)]
    have e2 : ρ (g * z) u = ω z • ρ g u := by
      rw [map_mul, Module.End.mul_apply, hωρ z hz, map_smul]
    rw [e1, e2, map_smul, smul_eq_mul, smul_smul]
    congr 1
    linear_combination f (π g⁻¹ w) * hω z hz
  · have e1 : π (g * k)⁻¹ w = π k⁻¹ (π g⁻¹ w) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [e1, hf _ (inv_mem hk), map_mul, Module.End.mul_apply, hu k hk]

theorem mem_smoothVectors_dual_of_inv (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) : f ∈ smoothVectors (Representation.dual π) :=
  mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hf)

theorem finite_support_coeffSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (w : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => f (π q.out⁻¹ w) • ρ q.out u :=
  finite_support_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) hKo
    (isCompactModCenter_matrixCoeff hπ hsc w (mem_smoothVectors_dual_of_inv hKo hf)).comp_inv
    fun g h0 => by
      change f (π g⁻¹ w) = 0 at h0
      simp only [h0, zero_smul]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hKo : IsOpen (K : Set (GL (Fin n) F)))
  (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
  (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K)

include hπ hsc hKo hf in
theorem coeffSum_add (w₁ w₂ : V) :
    coeffSum π ρ K f u (w₁ + w₂) = coeffSum π ρ K f u w₁ + coeffSum π ρ K f u w₂ := by
  unfold coeffSum quotSum
  rw [← finsum_add_distrib (finite_support_coeffSum hπ hsc hKo hf w₁)
    (finite_support_coeffSum hπ hsc hKo hf w₂)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_add, map_add, add_smul]

include hπ hsc hKo hf in
theorem coeffSum_smul (c : ℂ) (w : V) :
    coeffSum π ρ K f u (c • w) = c • coeffSum π ρ K f u w := by
  unfold coeffSum quotSum
  rw [smul_finsum' c (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_smul, map_smul, smul_eq_mul, mul_smul]

include hπ hsc hKo hωπ hωρ hω hf hu in

theorem coeffSum_act (x : GL (Fin n) F) (w : V) :
    coeffSum π ρ K f u (π x w) = ρ x (coeffSum π ρ K f u w) := by
  have hΨ := coeffSum_summand_rightInv hωπ hωρ hω hf hu w
  have hΨ' : ∀ g, ∀ h ∈ centerSup K, ρ x (f (π (g * h)⁻¹ w) • ρ (g * h) u) =
      ρ x (f (π g⁻¹ w) • ρ g u) := fun g h hh => by rw [hΨ g h hh]
  calc coeffSum π ρ K f u (π x w)
      = quotSum (centerSup K) fun g => ρ x (f (π (x⁻¹ * g)⁻¹ w) • ρ (x⁻¹ * g) u) := by
        refine quotSum_congr fun g => ?_
        have h1 : (x⁻¹ * g)⁻¹ = g⁻¹ * x := by group
        rw [map_smul, h1, map_mul π g⁻¹ x, Module.End.mul_apply, ← Module.End.mul_apply (ρ x),
          ← map_mul ρ, mul_inv_cancel_left]
    _ = quotSum (centerSup K) fun g => ρ x (f (π g⁻¹ w) • ρ g u) :=
        quotSum_mul_left (Φ := fun g => ρ x (f (π g⁻¹ w) • ρ g u)) hΨ' x⁻¹
    _ = ρ x (coeffSum π ρ K f u w) :=
        (linearMap_finsum (ρ x) (finite_support_coeffSum hπ hsc hKo hf w)).symm

def coeffMap : Representation.IntertwiningMap π ρ where
  toFun := coeffSum π ρ K f u
  map_add' := coeffSum_add hπ hsc hKo hf
  map_smul' := coeffSum_smul hπ hsc hKo hf
  isIntertwining' x := LinearMap.ext fun w => coeffSum_act hπ hsc hKo hωπ hωρ hω hf hu x w

theorem coeffMap_apply (w : V) :
    coeffMap hπ hsc hKo hωπ hωρ hω hf hu w = coeffSum π ρ K f u w := rfl

omit hωπ hωρ hω hu in
include hπ hsc hKo hf in

theorem map_coeffSum {σ : Representation ℂ (GL (Fin n) F) W}
    (p : Representation.IntertwiningMap ρ σ) (w : V) :
    p (coeffSum π ρ K f u w) = coeffSum π σ K f (p u) w := by
  unfold coeffSum quotSum
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  rw [Representation.IntertwiningMap.toLinearMap_apply, map_smul,
    Representation.IntertwiningMap.isIntertwining]

end CoeffSum

section Scalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {v : V} {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hωπ : HasCentralChar π ω)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hv : v ∈ fixedVectors π K) :
    ∃ c : ℂ, ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ).2
    (coeffMap hπ hsc hKo hωπ hωπ (fun z hz => hωπ.inv_mul hu₀ hz) hf hv)
  refine ⟨c, fun w => ?_⟩
  have := congrArg (fun φ : Representation.IntertwiningMap π π => φ w) hc
  simpa [coeffMap_apply] using this.symm

end Scalar

end Parabolic

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Topology ComplexConjugate
open scoped Pointwise

theorem quotSum_eq_zero_of_nonneg {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hΦ : ∀ g, 0 ≤ Φ g) (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out)
    (h0 : quotSum H Φ = 0) (q : G ⧸ H) : Φ q.out = 0 := by
  classical
  have hfin' : (support fun q : G ⧸ H => Φ q.out).Finite := hfin
  rw [quotSum_def, finsum_eq_sum_of_support_subset _ hfin'.coe_toFinset.symm.subset] at h0
  by_cases hq : q ∈ hfin'.toFinset
  · exact (Finset.sum_eq_zero_iff_of_nonneg fun q _ => hΦ q.out).1 h0 q hq
  · simpa using hq

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section ScalarDet

def scalarDet : GL (Fin n) F →* GL (Fin n) F :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp Matrix.GeneralLinearGroup.det

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coe_scalarDet (g : GL (Fin n) F) :
    ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.scalar (Fin n) (g : Matrix (Fin n) (Fin n) F).det := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem scalarDet_mem_center (g : GL (Fin n) F) :
    scalarDet g ∈ Subgroup.center (GL (Fin n) F) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, (coe_scalarDet g).symm⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem scalarDet_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    scalarDet z = z ^ n := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hdet : (z : Matrix (Fin n) (Fin n) F).det = a ^ n := by
    rw [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  ext1
  rw [coe_scalarDet, Units.val_pow_eq_pow_val, hdet, ← ha, map_pow]

theorem continuous_scalarDet : Continuous (scalarDet : GL (Fin n) F → GL (Fin n) F) := by
  have hval : Continuous fun g : GL (Fin n) F =>
      ((scalarDet g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    simp only [coe_scalarDet, Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.matrix_det)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  exact (hval.comp continuous_inv).congr fun g => by simp only [Function.comp_apply, map_inv]

end ScalarDet

section NormChar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

def normChar (ω : GL (Fin n) F → ℂ) (g : GL (Fin n) F) : ℝ :=
  ‖ω (scalarDet g)‖ ^ ((n : ℝ)⁻¹)

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.ne_zero {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ω z ≠ 0 := fun h0 => by
  have := hωπ.inv_mul hv hz
  rw [h0, mul_zero] at this
  exact zero_ne_one this

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_pos (g : GL (Fin n) F) : 0 < normChar ω g :=
  Real.rpow_pos_of_pos (norm_pos_iff.2 (hωπ.ne_zero hv (scalarDet_mem_center g))) _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_mul (x y : GL (Fin n) F) :
    normChar ω (x * y) = normChar ω x * normChar ω y := by
  unfold normChar
  rw [map_mul, hωπ.mul hv (scalarDet_mem_center x) (scalarDet_mem_center y), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_one : normChar ω (1 : GL (Fin n) F) = 1 := by
  unfold normChar
  rw [map_one, hωπ.one hv, norm_one, Real.one_rpow]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem normChar_inv_mul (g : GL (Fin n) F) : normChar ω g⁻¹ * normChar ω g = 1 := by
  rw [← normChar_mul hωπ hv, inv_mul_cancel, normChar_one hωπ hv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem map_pow_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (m : ℕ) : ω (z ^ m) = ω z ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, hωπ.one hv]
  | succ m ih => rw [pow_succ, hωπ.mul hv (pow_mem hz m) hz, ih, pow_succ]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normChar_of_mem_center {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    normChar ω z = ‖ω z‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : z = 1 := Units.ext (Subsingleton.elim _ _)
    rw [h1, normChar_one hωπ hv, hωπ.one hv, norm_one]
  · unfold normChar
    rw [scalarDet_of_mem_center hz, map_pow_of_mem_center hωπ hv hz, norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne']

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normChar_eq_one {k : GL (Fin n) F} (hk : π (scalarDet k) v = v) : normChar ω k = 1 := by
  have h1 : ω (scalarDet k) • v = (1 : ℂ) • v := by
    rw [one_smul, ← hωπ _ (scalarDet_mem_center k), hk]
  unfold normChar
  rw [smul_left_injective ℂ hv h1, norm_one, Real.one_rpow]

end NormChar

section Twisted

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}

variable (π ω) in

def twVec (x : V) (g : GL (Fin n) F) : V :=
  ((normChar ω g : ℂ)⁻¹) • π g x

variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_center (x : V) (g : GL (Fin n) F) {z : GL (Fin n) F}
    (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    twVec π ω x (g * z) = (ω z / (‖ω z‖ : ℂ)) • twVec π ω x g := by
  unfold twVec
  have hnz : (‖ω z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.2 (hωπ.ne_zero hv hz)).ne'
  have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv g).ne'
  rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul, smul_smul, smul_smul,
    normChar_mul hωπ hv, normChar_of_mem_center hωπ hv hz]
  congr 1
  push_cast
  field_simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul_of_mem {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) (g : GL (Fin n) F) {k : GL (Fin n) F} (hk : k ∈ K) :
    twVec π ω x (g * k) = twVec π ω x g := by
  unfold twVec
  rw [map_mul, Module.End.mul_apply, hx k hk, normChar_mul hωπ hv, hK k hk, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_mul (x : V) (a g : GL (Fin n) F) :
    twVec π ω x (a * g) = ((normChar ω a : ℂ)⁻¹) • π a (twVec π ω x g) := by
  unfold twVec
  rw [map_smul, smul_smul, map_mul, Module.End.mul_apply, normChar_mul hωπ hv]
  push_cast
  rw [mul_inv, mul_comm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem twVec_one (x : V) : twVec π ω x 1 = x := by
  unfold twVec
  rw [normChar_one hωπ hv, map_one, Module.End.one_apply]
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem conj_mul_self_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    conj (ω z / (‖ω z‖ : ℂ)) * (ω z / (‖ω z‖ : ℂ)) = 1 := by
  have h1 : ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]
  rw [Complex.conj_mul', h1]
  norm_num

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem norm_twVec_unit {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    ‖ω z / (‖ω z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 (hωπ.ne_zero hv hz))]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem normSq_twVec_rightInv {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1) :
    ∀ g, ∀ h ∈ centerSup K, ‖f (twVec π ω x (g * h))‖ ^ 2 = ‖f (twVec π ω x g)‖ ^ 2 := by
  refine rightInv_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) (fun g z hz => ?_)
    (fun g k hk => ?_)
  ·     rw [twVec_mul_center hωπ hv x g hz, map_smul, smul_eq_mul, norm_mul,
      norm_twVec_unit hωπ hv hz, one_mul]
  ·     rw [twVec_mul_of_mem hωπ hv hx hK g hk]

end Twisted

section Nonvanishing

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}

theorem quotSum_ofReal {G : Type*} [Group G] {H : Subgroup G} {Φ : G → ℝ}
    (hfin : HasFiniteSupport fun q : G ⧸ H => Φ q.out) :
    quotSum H (fun g => (Φ g : ℂ)) = ((quotSum H Φ : ℝ) : ℂ) := by
  rw [quotSum_def, quotSum_def]
  exact (map_finsum Complex.ofRealHom hfin).symm

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) {v : V}
  (hv : v ≠ 0) {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
  {f : Module.Dual ℂ V} (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x)

include hπ hsc hωπ hv hKo hf

omit hωπ hv in
theorem finite_support_normSq_twVec (x : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => ‖f (twVec π ω x q.out)‖ ^ 2 :=
  finite_support_centerSup (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2) hKo
    (isCompactModCenter_matrixCoeff hπ hsc x (mem_smoothVectors_dual_of_inv hKo hf))
    fun g h0 => by
      change f (π g x) = 0 at h0
      simp [twVec, h0]

theorem apply_eq_zero_of_quotSum_normSq {x : V} (hx : x ∈ fixedVectors π K)
    (hK : ∀ k ∈ K, normChar ω k = 1)
    (h0 : quotSum (centerSup K) (fun g => ‖f (twVec π ω x g)‖ ^ 2) = 0) : f x = 0 := by
  have h1 := quotSum_eq_zero_of_nonneg (fun g => by positivity)
    (finite_support_normSq_twVec hπ hsc hKo hf x) h0 (QuotientGroup.mk 1)
  rw [apply_out_mk (Φ := fun g => ‖f (twVec π ω x g)‖ ^ 2)
    (normSq_twVec_rightInv hωπ hv hx hK), twVec_one hωπ hv] at h1
  simpa using h1

end Nonvanishing

theorem exists_coeffSum_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} {ω : GL (Fin n) F → ℂ} [π.IsIrreducible]
    (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ w, coeffSum π π K f v w ≠ 0 := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have h1 : (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    (hπ v).mem_nhds (one_mem _)
  have hU : (stabilizerOf π v : Set (GL (Fin n) F)) ∩
      scalarDet ⁻¹' (stabilizerOf π v : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.inter_mem h1 (continuous_scalarDet.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  obtain ⟨K', hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  let K : Subgroup (GL (Fin n) F) := K'
  have hKo : IsOpen (K : Set (GL (Fin n) F)) := K'.isOpen
  have hKc' : IsCompact (K : Set (GL (Fin n) F)) := hKc
  have hvK : v ∈ fixedVectors π K := fun k hk => (hKU hk).1
  have hθK : ∀ k ∈ K, normChar ω k = 1 := fun k hk => normChar_eq_one hωπ hv0 (hKU hk).2
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Module.Dual ℂ V, f₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  let f : Module.Dual ℂ V := f₀ ∘ₗ (fixedVectors π K).subtype ∘ₗ fixedProj π hπ hKc' hKo
  have hf : ∀ k ∈ K, ∀ x, f (π k x) = f x := fun k hk x => by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_act hπ hKc' hKo hk]
  have hfv : f v = f₀ v := by
    simp only [f, LinearMap.comp_apply, fixedProj_apply_of_mem hπ hKc' hKo hvK,
      Submodule.subtype_apply]
  have hfs := mem_smoothVectors_dual_of_inv hKo hf

  let P : GL (Fin n) F → V := twVec π ω v
  let S : GL (Fin n) F → V := fun g => conj (f (P g)) • P g
  have hSfin : HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => S q.out :=
    finite_support_centerSup (Φ := S) hKo (isCompactModCenter_matrixCoeff hπ hsc v hfs)
      fun g h0 => by
        change f (π g v) = 0 at h0
        simp [S, P, twVec, h0]
  have hSinv : ∀ g, ∀ h ∈ centerSup K, S (g * h) = S g := by
    refine rightInv_centerSup (Φ := S) (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [S, P]
      rw [twVec_mul_center hωπ hv0 v g hz, map_smul, smul_eq_mul, map_mul, smul_smul]
      congr 1
      linear_combination conj (f (twVec π ω v g)) * conj_mul_self_unit hωπ hv0 hz
    · simp only [S, P]
      rw [twVec_mul_of_mem hωπ hv0 hvK hθK g hk]
  have hPk : ∀ k ∈ K, ∀ g, P (k * g) = π k (P g) := fun k hk g => by
    simp only [P]
    rw [twVec_mul hωπ hv0 v k g, hθK k hk, Complex.ofReal_one, inv_one, one_smul]
  let v' : V := quotSum (centerSup K) S
  have hv'K : v' ∈ fixedVectors π K := by
    intro k hk
    have hSk : ∀ g, π k (S g) = S (k * g) := fun g => by
      simp only [S]
      rw [hPk k hk, hf k hk, map_smul]
    calc π k v' = quotSum (centerSup K) fun g => π k (S g) :=
          linearMap_finsum (π k) hSfin
      _ = quotSum (centerSup K) fun g => S (k * g) := quotSum_congr hSk
      _ = v' := quotSum_mul_left hSinv k

  have hΨinv : ∀ a, ∀ g, ∀ h ∈ centerSup K,
      conj (f (P (g * h))) * f (P (a * (g * h))) = conj (f (P g)) * f (P (a * g)) := by
    intro a
    refine rightInv_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g)))
      (fun g z hz => ?_) (fun g k hk => ?_)
    · simp only [P]
      rw [← mul_assoc, twVec_mul_center hωπ hv0 v g hz, twVec_mul_center hωπ hv0 v (a * g) hz,
        f.map_smul, f.map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      linear_combination conj (f (twVec π ω v g)) * f (twVec π ω v (a * g)) *
        conj_mul_self_unit hωπ hv0 hz
    · simp only [P]
      rw [← mul_assoc, twVec_mul_of_mem hωπ hv0 hvK hθK g hk,
        twVec_mul_of_mem hωπ hv0 hvK hθK (a * g) hk]
  have hΨfin : ∀ a, HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      conj (f (P q.out)) * f (P (a * q.out)) := fun a =>
    finite_support_centerSup (Φ := fun g => conj (f (P g)) * f (P (a * g))) hKo
      (isCompactModCenter_matrixCoeff hπ hsc v hfs) fun g h0 => by
        change f (π g v) = 0 at h0
        simp [P, twVec, h0]

  let k' : GL (Fin n) F → ℂ := fun x => f (twVec π ω v' x)
  have hk'eq : ∀ x, k' x = quotSum (centerSup K) fun g => conj (f (P g)) * f (P (x * g)) := by
    intro x
    let L : V →ₗ[ℂ] ℂ := ((normChar ω x : ℂ)⁻¹) • (f ∘ₗ π x)
    have hL : ∀ y, L y = f (((normChar ω x : ℂ)⁻¹) • π x y) := fun y => by
      simp [L]
    calc k' x = L v' := (hL v').symm
      _ = quotSum (centerSup K) fun g => L (S g) := linearMap_finsum L hSfin
      _ = _ := quotSum_congr fun g => by
          simp only [hL, S, P]
          rw [twVec_mul hωπ hv0 v x g]
          simp only [map_smul, smul_eq_mul]
          ring
  have hk'conj : ∀ x, conj (k' x⁻¹) = k' x := by
    intro x
    rw [hk'eq, hk'eq, ← quotSum_mul_left (Φ := fun g => conj (f (P g)) * f (P (x * g)))
      (hΨinv x) x⁻¹, quotSum_def, quotSum_def,
      map_finsum (starRingEnd ℂ) (hΨfin x⁻¹)]
    refine finsum_congr fun q => ?_
    simp only [map_mul, Complex.conj_conj, mul_inv_cancel_left]
    ring
  have hfk : ∀ g, f (π g v') = (normChar ω g : ℂ) * k' g := fun g => by
    have hθ : (normChar ω g : ℂ) ≠ 0 := by exact_mod_cast (normChar_pos hωπ hv0 g).ne'
    simp only [k', twVec, map_smul, smul_eq_mul]
    field_simp
  refine ⟨K, hKc', hKo, f, hf, v', hv'K, v', fun hzero => hf₀ ?_⟩

  have hsum : quotSum (centerSup K) (fun g => f (π g⁻¹ v') * f (π g v')) = 0 := by
    have h2 := congrArg f hzero
    rw [map_zero] at h2
    unfold coeffSum at h2
    rw [quotSum_def, linearMap_finsum f (finite_support_coeffSum hπ hsc hKo hf v')] at h2
    rw [quotSum_def]
    simpa only [map_smul, smul_eq_mul] using h2
  have hterm : ∀ g, f (π g⁻¹ v') * f (π g v') = ((‖k' g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [hfk, hfk, ← hk'conj g⁻¹, inv_inv]
    have h2 : (normChar ω g⁻¹ : ℂ) * (normChar ω g : ℂ) = 1 := by
      exact_mod_cast normChar_inv_mul hωπ hv0 g
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    linear_combination (conj (k' g) * k' g) * h2
  have hk'0 : f v' = 0 := by
    refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hv'K hθK ?_
    rw [quotSum_congr hterm, quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v')]
      at hsum
    exact_mod_cast hsum

  have hk'1 : f v' = ((quotSum (centerSup K) fun g => ‖f (twVec π ω v g)‖ ^ 2 : ℝ) : ℂ) := by
    have h2 := hk'eq 1
    simp only [k', twVec_one hωπ hv0, one_mul] at h2
    rw [h2, ← quotSum_ofReal (finite_support_normSq_twVec (ω := ω) hπ hsc hKo hf v)]
    refine quotSum_congr fun g => ?_
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rw [← hfv]
  refine apply_eq_zero_of_quotSum_normSq hπ hsc hωπ hv0 hKo hf hvK hθK ?_
  rw [hk'1] at hk'0
  exact_mod_cast hk'0

end Parabolic

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul_ne_zero [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) :
    ∃ K : Subgroup (GL (Fin n) F), IsCompact (K : Set (GL (Fin n) F)) ∧
      IsOpen (K : Set (GL (Fin n) F)) ∧ ∃ f : Module.Dual ℂ V, (∀ k ∈ K, ∀ x, f (π k x) = f x) ∧
        ∃ v ∈ fixedVectors π K, ∃ c : ℂ, c ≠ 0 ∧ ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, w₀, hw₀⟩ := exists_coeffSum_ne_zero hπ hsc hωπ
  obtain ⟨c, hc⟩ := exists_coeffSum_eq_smul hπ hsc hKo hωπ hf hv
  refine ⟨K, hKc, hKo, f, hf, v, hv, c, fun h0 => hw₀ ?_, hc⟩
  rw [hc, h0, zero_smul]

theorem isSmooth_of_surjective (hρ : IsSmooth ρ) (p : Representation.IntertwiningMap ρ σ)
    (hp : Surjective p) : IsSmooth σ := by
  intro y
  obtain ⟨u, rfl⟩ := hp y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ u)
  rw [mem_stabilizerOf] at hg ⊢
  rw [← Representation.IntertwiningMap.isIntertwining, hg]

theorem exists_lift_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (p : Representation.IntertwiningMap ρ σ) (hp : Surjective p)
    (φ : Representation.IntertwiningMap π σ) :
    ∃ s : Representation.IntertwiningMap π ρ, p.comp s = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz
  have hσ := isSmooth_of_surjective hρ p hp
  have hφv : φ v ∈ fixedVectors σ K := map_mem_fixedVectors π φ hv
  obtain ⟨u, hu⟩ := fixedMap_surjective hρ hσ hKc hKo hp ⟨φ v, hφv⟩
  have hpu : p (u : U) = φ v := congrArg Subtype.val hu
  refine ⟨c⁻¹ • coeffMap hπ hsc hKo hωπ hωρ hω hf u.2, ?_⟩
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  change p (c⁻¹ • coeffSum π ρ K f (u : U) w) = φ w
  rw [map_smul, map_coeffSum hπ hsc hKo hf, hpu, ← map_coeffSum hπ hsc hKo hf, hc, map_smul,
    smul_smul, inv_mul_cancel₀ hc0, one_smul]

section Injective

variable (σ π) in

def pairingSum (K : Subgroup (GL (Fin n) F)) (ψ : Module.Dual ℂ W) (v : V) (b : W)
    (ũ : smoothVectors (Representation.dual π)) : ℂ :=
  quotSum (centerSup K) fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)

variable {K : Subgroup (GL (Fin n) F)} {ψ : Module.Dual ℂ W} {v : V}

theorem finite_support_pairingSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      ψ (σ q.out⁻¹ b) * (ũ : Module.Dual ℂ V) (π q.out v) :=
  finite_support_centerSup (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) hKo
    (isCompactModCenter_matrixCoeff hπ hsc v ũ.2) fun g h0 => by
      change (ũ : Module.Dual ℂ V) (π g v) = 0 at h0
      simp only [h0, mul_zero]

theorem pairingSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x) (hv : v ∈ fixedVectors π K) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ∀ g, ∀ h ∈ centerSup K, ψ (σ (g * h)⁻¹ b) * (ũ : Module.Dual ℂ V) (π (g * h) v) =
      ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) := by
  refine rightInv_centerSup
    (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : σ (g * z)⁻¹ b = ω z⁻¹ • σ g⁻¹ b := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωσ _ (inv_mem hz)]
    have e2 : π (g * z) v = ω z • π g v := by
      rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul]
    simp only [e1, e2, map_smul, smul_eq_mul]
    linear_combination ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) * hω z hz
  · have e1 : σ (g * k)⁻¹ b = σ k⁻¹ (σ g⁻¹ b) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [e1, hψ _ (inv_mem hk), map_mul, Module.End.mul_apply, hv k hk]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
  (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
  (hv : v ∈ fixedVectors π K)

include hπ hsc hωπ hωσ hω hKo hψ hv

omit hπ hsc hKo in

theorem pairingSum_act (h : GL (Fin n) F) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) := by
  unfold pairingSum
  rw [← quotSum_mul_left (pairingSum_summand_rightInv hωπ hωσ hω hψ hv (σ h b) ũ) h]
  refine quotSum_congr fun g => ?_
  rw [contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (σ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_mul, Module.End.mul_apply]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add (b : W) (ũ₁ ũ₂ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (ũ₁ + ũ₂) = pairingSum π σ K ψ v b ũ₁ + pairingSum π σ K ψ v b ũ₂ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b ũ₁)
    (finite_support_pairingSum hπ hsc hKo b ũ₂)]
  refine finsum_congr fun q => ?_
  simp only [Submodule.coe_add, LinearMap.add_apply, mul_add]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul (b : W) (c : ℂ) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (c • ũ) = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hωπ hωσ hω hψ hv in
theorem pairingSum_add_left (b₁ b₂ : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (b₁ + b₂) ũ = pairingSum π σ K ψ v b₁ ũ + pairingSum π σ K ψ v b₂ ũ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b₁ ũ)
    (finite_support_pairingSum hπ hsc hKo b₂ ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_add, add_mul]

omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul_left (c : ℂ) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (c • b) ũ = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_smul, smul_eq_mul]
  ring

omit hωπ hωσ hω hψ hv in

def pairingForm (b : W) : Module.Dual ℂ (smoothVectors (Representation.dual π)) where
  toFun := pairingSum π σ K ψ v b
  map_add' := pairingSum_add hπ hsc hKo b
  map_smul' c ũ := pairingSum_smul hπ hsc hKo b c ũ

theorem pairingForm_mem (hσ : IsSmooth σ) (b : W) :
    pairingForm (σ := σ) hπ hsc hKo (K := K) (ψ := ψ) (v := v) b ∈
      smoothVectors (Representation.dual (contragredient π)) := by
  rw [mem_smoothVectors]
  refine Subgroup.isOpen_mono (fun h hh => ?_) (hσ b)
  rw [mem_stabilizerOf] at hh ⊢
  refine LinearMap.ext fun ũ => ?_
  rw [dual_apply_apply]
  change pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) = pairingSum π σ K ψ v b ũ
  rw [← pairingSum_act hωπ hωσ hω hψ hv, hh]

omit hπ hsc hωπ hωσ hω hKo hψ hv in

def pairingMap (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
    (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) :
    Representation.IntertwiningMap σ (contragredient (contragredient π)) where
  toFun b := ⟨pairingForm (σ := σ) hπ hsc hKo b, pairingForm_mem hπ hsc hωπ hωσ hω hKo hψ hv hσ b⟩
  map_add' b₁ b₂ := Subtype.ext (LinearMap.ext fun ũ => pairingSum_add_left hπ hsc hKo b₁ b₂ ũ)
  map_smul' c b := Subtype.ext (LinearMap.ext fun ũ => pairingSum_smul_left hπ hsc hKo c b ũ)
  isIntertwining' h := LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun ũ => by
    change pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ)
    exact pairingSum_act hωπ hωσ hω hψ hv h b ũ)

omit hπ hsc hωπ hωσ hω hKo hψ hv in
theorem pairingMap_apply_apply (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ((pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ b :
      smoothVectors (Representation.dual (contragredient π))) :
        Module.Dual ℂ (smoothVectors (Representation.dual π))) ũ = pairingSum π σ K ψ v b ũ := rfl

end Injective

theorem exists_extend_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hωσ : HasCentralChar σ ω) (i : Representation.IntertwiningMap ρ σ) (hi : Injective i)
    (φ : Representation.IntertwiningMap ρ π) :
    ∃ Φ : Representation.IntertwiningMap σ π, Φ.comp i = φ := by
  obtain ⟨K, hKc, hKo, f, hf, v, hv, c, hc0, hc⟩ := exists_coeffSum_eq_smul_ne_zero hπ hsc hωπ
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1 :=
    fun z hz => hωπ.inv_mul hu₀ hz

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective i.toLinearMap
    (LinearMap.ker_eq_bot.2 hi)
  let ψ : Module.Dual ℂ W := (f ∘ₗ φ.toLinearMap ∘ₗ l) ∘ₗ (fixedVectors σ K).subtype ∘ₗ
    fixedProj σ hσ hKc hKo
  have hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x := fun k hk x => by
    simp only [ψ, LinearMap.comp_apply, fixedProj_apply_act hσ hKc hKo hk]
  have hψi : ∀ u, ψ (i u) = f (φ u) := by
    have h := eq_of_invariant_of_eqOn hρ hKc hKo (f := ψ ∘ₗ i.toLinearMap)
      (g := f ∘ₗ φ.toLinearMap)
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hψ k hk])
      (fun k hk u => by
        simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining, hf k hk])
      (fun u hu => by
        have hiu : i u ∈ fixedVectors σ K := map_mem_fixedVectors ρ i hu
        have hl' : l (i u) = u := LinearMap.congr_fun hl u
        simp only [ψ, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Submodule.subtype_apply, fixedProj_apply_of_mem hσ hKc hKo hiu, hl'])
    exact fun u => LinearMap.congr_fun h u

  have hπa := isAdmissible_of_isIrreducible hπ
  let e := (toDoubleContragredient hπa.1).ofBijective (toDoubleContragredient_bijective hπa)
  let Φ₀ := pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ
  refine ⟨c⁻¹ • (e.symm.toIntertwiningMap.comp Φ₀), ?_⟩
  have key : ∀ u, Φ₀ (i u) = c • toDoubleContragredient hπa.1 (φ u) := fun u =>
    Subtype.ext (LinearMap.ext fun ũ => by
      rw [pairingMap_apply_apply]
      change pairingSum π σ K ψ v (i u) ũ = c * (ũ : Module.Dual ℂ V) (φ u)
      unfold pairingSum
      calc quotSum (centerSup K) (fun g => ψ (σ g⁻¹ (i u)) * (ũ : Module.Dual ℂ V) (π g v))
          = quotSum (centerSup K) (fun g => (ũ : Module.Dual ℂ V) (f (π g⁻¹ (φ u)) • π g v)) :=
            quotSum_congr fun g => by
              rw [← Representation.IntertwiningMap.isIntertwining, hψi,
                Representation.IntertwiningMap.isIntertwining, map_smul, smul_eq_mul]
        _ = (ũ : Module.Dual ℂ V) (coeffSum π π K f v (φ u)) :=
            (linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf (φ u))).symm
        _ = c * (ũ : Module.Dual ℂ V) (φ u) := by rw [hc, map_smul, smul_eq_mul])
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
  change c⁻¹ • e.symm (Φ₀ (i u)) = φ u
  rw [key, map_smul]
  change c⁻¹ • c • e.symm (e (φ u)) = φ u
  rw [Representation.Equiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end Parabolic

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Constructions

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}

def subrepIncl (Y : Subrepresentation ρ) :
    Representation.IntertwiningMap Y.toRepresentation ρ where
  toLinearMap := Y.toSubmodule.subtype
  isIntertwining' _ := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem subrepIncl_apply (Y : Subrepresentation ρ) (y : Y.toSubmodule) :
    subrepIncl Y y = (y : U) := rfl

theorem isSmooth_toRepresentation (hρ : IsSmooth ρ) (Y : Subrepresentation ρ) :
    IsSmooth Y.toRepresentation := by
  intro y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ (y : U))
  rw [mem_stabilizerOf] at hg ⊢
  exact Subtype.ext hg

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.toRepresentation (hωρ : HasCentralChar ρ ω) (Y : Subrepresentation ρ) :
    HasCentralChar Y.toRepresentation ω := fun z hz y => Subtype.ext (hωρ z hz y)

theorem isSmooth_prod (hπ : IsSmooth π) (hρ : IsSmooth ρ) : IsSmooth (π.prod ρ) := by
  intro x
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf π x.1 ⊓ stabilizerOf ρ x.2) (fun g hg => ?_)
    ((hπ x.1).inter (hρ x.2))
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  rw [mem_stabilizerOf] at h1 h2 ⊢
  exact Prod.ext h1 h2

variable (π) in

def piRep (m : ℕ) : Representation ℂ (GL (Fin n) F) (Fin m → V) where
  toFun g := LinearMap.pi fun i => π g ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
@[simp]
theorem piRep_apply (m : ℕ) (g : GL (Fin n) F) (x : Fin m → V) (i : Fin m) :
    piRep π m g x i = π g (x i) := rfl

theorem isSmooth_piRep (hπ : IsSmooth π) (m : ℕ) : IsSmooth (piRep π m) := by
  intro x
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h : ⋂ i, (stabilizerOf π (x i) : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.iInter_mem.2 fun i => (hπ (x i)).mem_nhds (one_mem _)
  refine Filter.mem_of_superset h fun g hg => ?_
  rw [SetLike.mem_coe, mem_stabilizerOf]
  funext i
  exact (Set.mem_iInter.1 hg i)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.piRep (hωπ : HasCentralChar π ω) (m : ℕ) :
    HasCentralChar (piRep π m) ω := fun z hz x => funext fun i => hωπ z hz (x i)

variable (π) in

def piIncl (m : ℕ) (i : Fin m) : Representation.IntertwiningMap π (piRep π m) where
  toLinearMap := LinearMap.single ℂ (fun _ => V) i
  isIntertwining' g := by
    ext x j
    by_cases h : j = i
    · subst h; simp
    · simp [h]

variable (π) in

def piProj (m : ℕ) (i : Fin m) : Representation.IntertwiningMap (piRep π m) π where
  toLinearMap := LinearMap.proj i
  isIntertwining' _ := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem piIncl_apply (m : ℕ) (i : Fin m) (x : V) : piIncl π m i x = Pi.single i x := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem piProj_apply (m : ℕ) (i : Fin m) (x : Fin m → V) : piProj π m i x = x i := rfl

end Constructions

section Detect

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}

theorem exists_retraction [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
    (Y : Subrepresentation ρ) (t : Representation.IntertwiningMap π ρ)
    (ht : ∀ x, t x ∈ Y.toSubmodule → x = 0) :
    ∃ Fm : Representation.IntertwiningMap ρ π, (∀ x, Fm (t x) = x) ∧
      ∀ y ∈ Y.toSubmodule, Fm y = 0 := by
  let j : Representation.IntertwiningMap (π.prod Y.toRepresentation) ρ :=
    t.comp (Representation.IntertwiningMap.fst ℂ π Y.toRepresentation) +
      (subrepIncl Y).comp (Representation.IntertwiningMap.snd ℂ π Y.toRepresentation)
  have hj : ∀ p : V × Y.toSubmodule, j p = t p.1 + (p.2 : U) := fun p => rfl
  have hjinj : Injective j := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hj] at hp
    have h1 : p.1 = 0 := ht p.1 (by
      rw [eq_neg_of_add_eq_zero_left hp]
      exact Y.toSubmodule.neg_mem p.2.2)
    have h2 : (p.2 : U) = 0 := by rw [h1, map_zero, zero_add] at hp; exact hp
    exact Prod.ext h1 (Subtype.ext h2)
  obtain ⟨Fm, hFm⟩ := exists_extend_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_prod hπ (isSmooth_toRepresentation hρ Y)) hρ hωρ j hjinj
    (Representation.IntertwiningMap.fst ℂ π Y.toRepresentation)
  have hF : ∀ p, Fm (j p) = p.1 := fun p =>
    congrArg (fun φ : Representation.IntertwiningMap (π.prod Y.toRepresentation) π => φ p) hFm
  refine ⟨Fm, fun x => ?_, fun y hy => ?_⟩
  · have := hF (x, 0)
    rwa [hj, ZeroMemClass.coe_zero, add_zero] at this
  · have := hF (0, ⟨y, hy⟩)
    rwa [hj, map_zero, zero_add] at this

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem iSup_range_stable (s : Finset (Representation.IntertwiningMap π ρ))
    (g : GL (Fin n) F) {y : U}
    (hy : y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) :
    ρ g y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap := by
  have hle : (⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) ≤
      (⨆ t ∈ s, LinearMap.range
        (t : Representation.IntertwiningMap π ρ).toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining]
    exact (le_iSup₂ (f := fun t (_ : t ∈ s) =>
      LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) t ht) ⟨π g x, rfl⟩
  exact hle hy

theorem exists_apply_ne_zero_of_mem_iSup [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (s : Finset (Representation.IntertwiningMap π ρ)) :
    ∀ y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap,
      y ≠ 0 → ∃ Fm : Representation.IntertwiningMap ρ π, Fm y ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy hy0
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hy
    exact absurd hy hy0
  | insert t s hts ih =>
    intro y hy hy0
    rw [Finset.iSup_insert] at hy
    obtain ⟨a, ⟨w, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    by_cases hyY : t w + b ∈
        ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap
    · exact ih _ hyY hy0
    · let Y : Subrepresentation ρ :=
        ⟨⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap,
          fun g _ hy => iSup_range_stable s g hy⟩
      let L : Subrepresentation π :=
        ⟨Y.toSubmodule.comap t.toLinearMap, fun g x hx => by
          rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
            Representation.IntertwiningMap.isIntertwining]
          exact Y.apply_mem_toSubmodule g hx⟩
      have hL : ∀ x, t x ∈ Y.toSubmodule → x = 0 := by
        rcases eq_bot_or_eq_top L with h | h
        · intro x hx
          have hxL : x ∈ L.toSubmodule := hx
          rw [h] at hxL
          exact (Submodule.mem_bot ℂ).1 hxL
        · exfalso
          have hwL : w ∈ L.toSubmodule := by rw [h]; exact Submodule.mem_top
          exact hyY (Y.toSubmodule.add_mem hwL hb)
      obtain ⟨Fm, hFt, hFY⟩ := exists_retraction hπ hsc hωπ hρ hωρ Y t hL
      refine ⟨Fm, ?_⟩
      rw [map_add, Representation.IntertwiningMap.toLinearMap_apply, hFt, hFY b hb, add_zero]
      rintro rfl
      exact hyY (by rw [map_zero, zero_add]; exact hb)

end Detect

section Isotypic

variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}

variable (π ρ) in

def isotypicPart : Submodule ℂ U :=
  ⨆ t : Representation.IntertwiningMap π ρ, LinearMap.range t.toLinearMap

variable (π ρ) in

def isotypicKernel : Submodule ℂ U :=
  ⨅ Fm : Representation.IntertwiningMap ρ π, LinearMap.ker Fm.toLinearMap

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_isotypicKernel {u : U} :
    u ∈ isotypicKernel π ρ ↔ ∀ Fm : Representation.IntertwiningMap ρ π, Fm u = 0 := by
  simp only [isotypicKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    Representation.IntertwiningMap.toLinearMap_apply]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem apply_mem_isotypicPart (t : Representation.IntertwiningMap π ρ) (x : V) :
    t x ∈ isotypicPart π ρ :=
  (le_iSup (fun t : Representation.IntertwiningMap π ρ => LinearMap.range t.toLinearMap) t)
    ⟨x, rfl⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem isotypicPart_stable (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicPart π ρ) :
    ρ g u ∈ isotypicPart π ρ := by
  have hle : isotypicPart π ρ ≤ (isotypicPart π ρ).comap (ρ g) := by
    refine iSup_le fun t => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining]
    exact apply_mem_isotypicPart t (π g x)
  exact hle hu

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem isotypicKernel_stable (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicKernel π ρ) :
    ρ g u ∈ isotypicKernel π ρ := by
  rw [mem_isotypicKernel] at hu ⊢
  intro Fm
  rw [Representation.IntertwiningMap.isIntertwining, hu, map_zero]

variable [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
  (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
include hπ hsc hωπ hρ hωρ

theorem disjoint_isotypicPart_isotypicKernel :
    Disjoint (isotypicPart π ρ) (isotypicKernel π ρ) := by
  rw [Submodule.disjoint_def]
  intro y hy1 hy2
  by_contra hy0
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hy1
  obtain ⟨Fm, hFm⟩ := exists_apply_ne_zero_of_mem_iSup hπ hsc hωπ hρ hωρ s y hs hy0
  exact hFm (mem_isotypicKernel.1 hy2 Fm)

theorem exists_sub_mem_isotypicKernel (u : U) :
    ∃ u' ∈ isotypicPart π ρ, u - u' ∈ isotypicKernel π ρ := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hπa := isAdmissible_of_isIrreducible hπ
  obtain ⟨K, hKc, hKo, huK⟩ := (isSmooth_iff_forall_exists ρ).1 hρ u

  let ev : Representation.IntertwiningMap ρ π →ₗ[ℂ] V :=
    { toFun := fun Fm => Fm u, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let E := LinearMap.range ev
  have hEK : E ≤ fixedVectors π K := by
    rintro _ ⟨Fm, rfl⟩
    exact map_mem_fixedVectors ρ Fm huK
  have : FiniteDimensional ℂ (fixedVectors π K) := hπa.2 K hKc hKo
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hEK
  let m := Module.finrank ℂ E
  let bE := Module.finBasis ℂ E
  have hb : ∀ i, ∃ Gi : Representation.IntertwiningMap ρ π, Gi u = (bE i : V) :=
    fun i => (bE i).2
  choose Gs hGs using hb

  let Γ : Representation.IntertwiningMap ρ (piRep π m) :=
    { toLinearMap := LinearMap.pi fun i => (Gs i).toLinearMap
      isIntertwining' := fun g => by
        ext x i
        simp [Representation.IntertwiningMap.isIntertwining] }
  have hΓ : ∀ x i, Γ x i = Gs i x := fun _ _ => rfl

  let W0 : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g => ρ g u), fun g x hx => by
      have hle : Submodule.span ℂ (Set.range fun h => ρ h u) ≤
          (Submodule.span ℂ (Set.range fun h => ρ h u)).comap (ρ g) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
      exact hle hx⟩
  have huW0 : u ∈ W0.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have hvanish : ∀ H : Representation.IntertwiningMap ρ π, H u = 0 →
      ∀ x ∈ W0.toSubmodule, H x = 0 := by
    intro H hH x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      rw [Representation.IntertwiningMap.isIntertwining, hH, map_zero]
    | zero => exact map_zero H
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, ha, smul_zero]
  let Γ0 := Γ.comp (subrepIncl W0)
  have hΓ0 : ∀ x i, Γ0 x i = Gs i (x : U) := fun _ _ => rfl
  have hρ0 := isSmooth_toRepresentation hρ W0
  have hωρ0 := hωρ.toRepresentation W0

  have hsurj : Surjective Γ0 := by
    by_contra hns
    let R : Subrepresentation (piRep π m) := Γ0.range
    have hRmem : ∀ y, y ∈ R.toSubmodule ↔ ∃ x, Γ0 x = y := fun y => Iff.rfl
    have hR : ∃ j, ∀ x, piIncl π m j x ∈ R.toSubmodule → x = 0 := by
      by_contra hall
      push Not at hall
      apply hns
      have hsub : ∀ j, ∀ x, piIncl π m j x ∈ R.toSubmodule := by
        intro j
        obtain ⟨x₀, hx₀R, hx₀⟩ := hall j
        let L : Subrepresentation π :=
          ⟨R.toSubmodule.comap (piIncl π m j).toLinearMap, fun g x hx => by
            rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
            exact R.apply_mem_toSubmodule g hx⟩
        rcases eq_bot_or_eq_top L with h | h
        · exfalso
          have hx₀L : x₀ ∈ L.toSubmodule := hx₀R
          rw [h] at hx₀L
          exact hx₀ ((Submodule.mem_bot ℂ).1 hx₀L)
        · intro x
          have hxL : x ∈ L.toSubmodule := by rw [h]; exact Submodule.mem_top
          exact hxL
      intro y
      have hy : y ∈ R.toSubmodule := by
        rw [← Finset.univ_sum_single y]
        exact Submodule.sum_mem _ fun j _ => hsub j (y j)
      exact (hRmem y).1 hy
    obtain ⟨j, hj⟩ := hR
    obtain ⟨Φ, hΦj, hΦR⟩ := exists_retraction hπ hsc hωπ (isSmooth_piRep hπ m)
      (hωπ.piRep m) R (piIncl π m j) hj
    have hc : ∀ i, ∃ c : ℂ, ∀ x, Φ (piIncl π m i x) = c • x := fun i => by
      obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ).2
        (Φ.comp (piIncl π m i))
      exact ⟨c, fun x =>
        (congrArg (fun ψ : Representation.IntertwiningMap π π => ψ x) hc).symm⟩
    choose c hcx using hc
    have hΦ : ∀ y : Fin m → V, Φ y = ∑ i, c i • y i := fun y => by
      conv_lhs => rw [← Finset.univ_sum_single y]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hcx i (y i)
    have hzero : ∑ i, c i • bE i = 0 := by
      have h1 : Φ (Γ u) = 0 := hΦR _ ((hRmem _).2 ⟨⟨u, huW0⟩, rfl⟩)
      rw [hΦ] at h1
      apply Subtype.ext
      simpa [hΓ, hGs] using h1
    have hcj : c j = 0 := (Fintype.linearIndependent_iff.1 bE.linearIndependent) c hzero j
    have h1 : (1 : ℂ) • u₀ = c j • u₀ := by rw [one_smul, ← hcx j u₀, hΦj]
    rw [hcj, zero_smul, one_smul] at h1
    exact hu₀ h1

  have hlift : ∀ i, ∃ s : Representation.IntertwiningMap π W0.toRepresentation,
      Γ0.comp s = piIncl π m i := fun i =>
    exists_lift_of_isSupercuspidal hπ hsc hωπ hρ0 hωρ0 Γ0 hsurj (piIncl π m i)
  choose s hs using hlift
  let u' : U := ∑ i, (s i (Gs i u) : U)
  have hu'W0 : u' ∈ W0.toSubmodule := Submodule.sum_mem _ fun i _ => (s i (Gs i u)).2
  have hGu' : ∀ i, Gs i u' = Gs i u := by
    intro i
    have h2 : Γ0 (∑ k, s k (Gs k u)) = Γ u := by
      rw [map_sum]
      have h3 : ∀ k, Γ0 (s k (Gs k u)) = Pi.single k (Gs k u) := fun k => by
        rw [← Representation.IntertwiningMap.comp_apply, hs]
        rfl
      simp only [h3]
      exact Finset.univ_sum_single (Γ u)
    have h4 := congrFun h2 i
    rw [hΓ0, hΓ] at h4
    simpa [u'] using h4
  refine ⟨u', Submodule.sum_mem _ fun i _ => apply_mem_isotypicPart ((subrepIncl W0).comp (s i))
    (Gs i u), ?_⟩
  rw [mem_isotypicKernel]
  intro Fm
  have hFE : Fm u ∈ E := ⟨Fm, rfl⟩
  let a := bE.repr ⟨Fm u, hFE⟩
  have hFu : Fm u = ∑ i, a i • (bE i : V) := by
    have h5 := congrArg Subtype.val (bE.sum_repr ⟨Fm u, hFE⟩)
    rw [Submodule.coe_sum] at h5
    simp only [Submodule.coe_smul] at h5
    exact h5.symm
  let H : Representation.IntertwiningMap ρ π := Fm - ∑ i, a i • Gs i
  have hHx : ∀ x, H x = Fm x - ∑ i, a i • Gs i x := fun x => by
    simp [H, Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  have hHu : H u = 0 := by
    rw [hHx, hFu]
    simp [hGs]
  have hHu' := hvanish H hHu u' hu'W0
  rw [hHx, sub_eq_zero] at hHu'
  rw [map_sub, hHu', hFu, sub_eq_zero]
  simp [hGu', hGs]

theorem isCompl_isotypicPart_isotypicKernel :
    IsCompl (isotypicPart π ρ) (isotypicKernel π ρ) := by
  refine ⟨disjoint_isotypicPart_isotypicKernel hπ hsc hωπ hρ hωρ,
    codisjoint_iff.2 (eq_top_iff.2 fun u _ => ?_)⟩
  obtain ⟨u', hu', h⟩ := exists_sub_mem_isotypicKernel hπ hsc hωπ hρ hωρ u
  exact Submodule.mem_sup.2 ⟨u', hu', u - u', h, add_sub_cancel u' u⟩

theorem not_surjective_of_le_isotypicKernel (A : Subrepresentation ρ)
    (hA : A.toSubmodule ≤ isotypicKernel π ρ)
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ (isSmooth_toRepresentation hρ A)
    (hωρ.toRepresentation A) p hp (Representation.IntertwiningMap.id π)
  have hps : ∀ x, p (s x) = x := fun x =>
    congrArg (fun φ : Representation.IntertwiningMap π π => φ x) hs
  let i := (subrepIncl A).comp s
  have hi : Injective i := fun x y hxy => by
    have h1 : s x = s y := Subtype.ext hxy
    rw [← hps x, ← hps y, h1]
  obtain ⟨Fm, hFm⟩ := exists_extend_of_isSupercuspidal hπ hsc hωπ hπ hρ hωρ i hi
    (Representation.IntertwiningMap.id π)
  have h1 : Fm (i x₀) = x₀ :=
    congrArg (fun φ : Representation.IntertwiningMap π π => φ x₀) hFm
  have h2 : Fm (i x₀) = 0 := mem_isotypicKernel.1 (hA (s x₀).2) Fm
  exact hx₀ (h1.symm.trans h2)

end Isotypic

end Parabolic

end GroundTheory.Automorphic
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem modularCharacter_eq_one_of_mem_center {H : Type*} [TopologicalSpace H] [Group H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] {g : H} (hg : g ∈ Subgroup.center H) :
    MeasureTheory.Measure.modularCharacter g = 1 := by
  change MeasureTheory.Measure.modularCharacterFun g = 1
  borelize H
  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor
    MeasureTheory.Measure.haar g]
  have hcomm : (fun x : H => x * g) = (fun x => g * x) :=
    funext fun x => Subgroup.mem_center_iff.1 hg x
  have key : MeasureTheory.Measure.map (fun x : H => x * g)
      (MeasureTheory.Measure.haar : MeasureTheory.Measure H) = MeasureTheory.Measure.haar := by
    rw [hcomm]
    exact MeasureTheory.map_mul_left_eq_self _ g
  calc MeasureTheory.Measure.haarScalarFactor
        (MeasureTheory.Measure.map (fun x : H => x * g)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H))
        (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
      = MeasureTheory.Measure.haarScalarFactor
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H)
          (MeasureTheory.Measure.haar : MeasureTheory.Measure H) := by congr 1
    _ = 1 := MeasureTheory.Measure.haarScalarFactor_self _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem center_le_levi {α : Type*} [LinearOrder α] (β : Fin n → α) :
    Subgroup.center (GL (Fin n) F) ≤ levi F n β := by
  intro z hz
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  rw [mem_levi]
  intro i j hij
  have hij' : i ≠ j := fun h => hij (h ▸ rfl)
  change (z : Matrix (Fin n) (Fin n) F) i j = 0
  rw [← ha, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij']

theorem sqrtModular_of_mem_center {α : Type*} [LinearOrder α] {β : Fin n → α}
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) :
    sqrtModular F n β ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ = 1 := by
  have hc : (⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ : blockUpper F n β) ∈
      Subgroup.center (blockUpper F n β) :=
    Subgroup.mem_center_iff.2 fun p => Subtype.ext (Subgroup.mem_center_iff.1 hz p)
  change ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = 1
  rw [modularCharacter_eq_one_of_mem_center hc]
  simp

theorem hasCentralChar_parabolicInd {α : Type*} [LinearOrder α] {β : Fin n → α}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ}
    (hτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w) :
    HasCentralChar (parabolicInd F n β τ) ω := by
  intro z hz f
  apply Subtype.ext
  funext x
  have hf := ((mem_parabolicIndSpace τ).1 f.2).1 ⟨z, levi_le_blockUpper (center_le_levi β hz)⟩ x
  change (f : GL (Fin n) F → W) (x * z) = ω z • (f : GL (Fin n) F → W) x
  rw [Subgroup.mem_center_iff.1 hz x]
  change (f : GL (Fin n) F → W) (z * x) = _ at hf
  rw [hf, sqrtModular_of_mem_center hz, one_smul, leviProj_of_mem_levi (center_le_levi β hz),
    hτ z hz]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem not_surjective_of_le_parabolicInd [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W}
    {ω : GL (Fin n) F → ℂ} (hωτ : HasCentralChar (parabolicInd F n β τ) ω)
    (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  intro hp
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hωπ : HasCentralChar π ω := by
    intro z hz x
    obtain ⟨a, rfl⟩ := hp x
    rw [← Representation.IntertwiningMap.isIntertwining, (hωτ.toRepresentation A) z hz a,
      map_smul]
  obtain ⟨s, hs⟩ := exists_lift_of_isSupercuspidal hπ hsc hωπ
    (isSmooth_toRepresentation (isSmooth_parabolicInd τ) A) (hωτ.toRepresentation A) p hp
    (Representation.IntertwiningMap.id π)
  let Φ := (subrepIncl A).comp s
  have hJ := hsc β hβ
  have h0 : frobeniusParabolic F n β τ hπ Φ = 0 :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      rfl)
  have hΦ : Φ = 0 := (frobeniusParabolic F n β τ hπ).injective (h0.trans (map_zero _).symm)
  have h1 : p (s u₀) = u₀ := congrArg (fun φ : Representation.IntertwiningMap π π => φ u₀) hs
  have h2 : s u₀ = 0 := Subtype.ext (congrArg (fun φ : Representation.IntertwiningMap π
    (parabolicInd F n β τ) => φ u₀) hΦ)
  rw [h2, map_zero] at h1
  exact hu₀ h1.symm

theorem not_surjective_of_isIrreducible [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) {β : Fin n → ℕ} (hβ : ∃ i j, β i ≠ β j) {W : Type*}
    [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (levi F n β) W} [τ.IsIrreducible]
    (hτ : IsSmooth τ) (A : Subrepresentation (parabolicInd F n β τ))
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by
  classical
  have hc : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∃ c : ℂ, ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = c • w := fun z hz =>
    exists_central_character hτ (Subgroup.mem_center_iff.2 fun m =>
      Subtype.ext (Subgroup.mem_center_iff.1 hz m))
  let ω : GL (Fin n) F → ℂ := fun z =>
    if hz : z ∈ Subgroup.center (GL (Fin n) F) then (hc z hz).choose else 0
  have hωτ : ∀ z (hz : z ∈ Subgroup.center (GL (Fin n) F)), ∀ w,
      τ ⟨z, center_le_levi β hz⟩ w = ω z • w := fun z hz w => by
    simp only [ω, dif_pos hz]
    exact (hc z hz).choose_spec w
  exact not_surjective_of_le_parabolicInd hπ hsc hβ (hasCentralChar_parabolicInd hωτ) A p

end Parabolic

end GroundTheory.Automorphic
end
end
