import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
import Formalism.WeaklyAdmissibleFiltrations.Statement

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filB_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

private theorem range_tensor_map_subtype_mono {S T : Submodule Qp BdR} (h : S ≤ T) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) S.subtype) ≤
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) T.subtype) := by
  rintro _ ⟨w, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact LinearMap.mem_range.mpr ⟨x ⊗ₜ[Qp] ⟨(y : BdR), h y.2⟩, by simp⟩
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂

theorem filVB_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  exact range_tensor_map_subtype_mono (S := (PD.Fil b).restrictScalars Qp) (T := (PD.Fil a).restrictScalars Qp)
    fun y hy => filB_anti PD hab hy

private theorem mem_FilV_iff' (a : ℤ) (z : V ⊗[Qp] BdR) :
    z ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ↔
      ∃ w, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil a).restrictScalars Qp).subtype w = z := Iff.rfl

theorem tmul_mem_filV (a : ℤ) (x : V) {y : BdR} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  (mem_FilV_iff' PD a _).mpr
    ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil a).restrictScalars Qp), by simp⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV PD a x ha⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    exact ⟨min a₁ a₂, add_mem (filVB_anti PD (min_le_left _ _) ha₁)
      (filVB_anti PD (min_le_right _ _) ha₂)⟩

theorem coord_mem {ι : Type} (b : Basis ι Qp V) (a : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V) a) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b z i ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := (mem_FilV_iff' PD a z).mp hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    exact Submodule.smul_of_tower_mem (PD.Fil a) _ y.2
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact add_mem h₁ h₂

theorem filV_sep (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  apply (TensorProduct.equivFinsuppOfBasisLeft (Basis.ofVectorSpace Qp V)).injective
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  refine PD.Fil_sep _ fun a => ?_
  convert coord_mem PD (Basis.ofVectorSpace Qp V) a z (hz a) i

private theorem exists_int_finset_subset_FilV (s : Finset (V ⊗[Qp] BdR)) :
    ∃ a : ℤ, ∀ z ∈ s, z ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨c, hc⟩ := filV_exh PD (LL := LL) x
    refine ⟨min a c, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact filVB_anti PD (min_le_right _ _) hc
    · exact filVB_anti PD (min_le_left _ _) (ha z hz)

theorem exists_le_filV (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ≤ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := D)).mp inferInstance
  obtain ⟨a, ha⟩ := exists_int_finset_subset_FilV PD (LL := LL) (V := V) s
  refine ⟨a, ?_⟩
  rw [← hs]
  exact Submodule.span_le.mpr fun z hz => ha z (Finset.mem_coe.mp hz)

theorem exists_inf_filV_eq_bot (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ⊓ FilV PD (LL := LL) (V := V) a = ⊥ := by
  let S : ℤ → Submodule LL D := fun a => (Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a).comap D.subtype
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL (S a) = n := ⟨_, 0, rfl⟩
  obtain ⟨a₀, ha₀⟩ := Nat.find_spec hex
  refine ⟨a₀, eq_bot_iff.mpr ?_⟩
  rintro x ⟨hxD, hxF⟩
  rw [Submodule.mem_bot]
  refine filV_sep PD (LL := LL) x fun b => ?_
  rcases le_total b a₀ with hb | hb
  · exact filVB_anti PD hb hxF
  · have hle : S b ≤ S a₀ := Submodule.comap_mono (filVB_anti PD hb)
    have heq : S b = S a₀ :=
      Submodule.eq_of_le_of_finrank_eq hle
        (le_antisymm (Submodule.finrank_mono hle) (ha₀ ▸ Nat.find_min' hex ⟨b, rfl⟩))
    have hx : (⟨x, hxD⟩ : D) ∈ S a₀ := hxF
    rw [← heq] at hx
    exact hx

end Fil

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Cnt

variable {LL : Type} [Field LL] {E : Type} [AddCommGroup E] [Module LL E]

def sumAt {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) : (Fin r → LL) →ₗ[LL] E :=
  ∑ m, (LinearMap.proj m : (Fin r → LL) →ₗ[LL] LL).smulRight (e m j)

theorem sumAt_apply {r : ℕ} (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    sumAt e j c = ∑ m, c m • e m j := by
  simp [sumAt, LinearMap.sum_apply]

def Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) :
    Submodule LL (Fin r → LL) :=
  ⨅ (i : ℤ) (_ : i < j), (Fil (-i + 1)).comap (sumAt e i)

theorem mem_Ub {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) (j : ℤ) (c : Fin r → LL) :
    c ∈ Ub Fil e j ↔ ∀ i < j, ∑ m, c m • e m i ∈ Fil (-i + 1) := by
  simp only [Ub, Submodule.mem_iInf, Submodule.mem_comap, sumAt_apply]

theorem Ub_anti {r : ℕ} (Fil : ℤ → Submodule LL E) (e : Fin r → ℤ → E) {j j' : ℤ} (h : j ≤ j') :
    Ub Fil e j' ≤ Ub Fil e j := fun c hc =>
  (mem_Ub Fil e j c).2 fun i hi => (mem_Ub Fil e j' c).1 hc i (by omega)

variable {r : ℕ} {Fil : ℤ → Submodule LL E} (hFa : Antitone Fil) (D : Submodule LL E)
  [FiniteDimensional LL D] {e : Fin r → ℤ → E}

include hFa in

theorem count_step (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (j : ℤ) :
    finrank LL ↥(Ub Fil e (j + 1)) + finrank LL ↥(D ⊓ Fil (-j)) =
      finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1)) := by
  let ψ : ↥(Ub Fil e j) →ₗ[LL] E ⧸ Fil (-j + 1) :=
    (Fil (-j + 1)).mkQ ∘ₗ sumAt e j ∘ₗ (Ub Fil e j).subtype
  have hle : Ub Fil e (j + 1) ≤ Ub Fil e j := Ub_anti Fil e (by omega)
  have hker : LinearMap.ker ψ = (Ub Fil e (j + 1)).comap (Ub Fil e j).subtype := by
    ext ⟨c, hc⟩
    simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, sumAt_apply]
    rw [mem_Ub]
    constructor
    · intro h i hi
      rcases lt_or_eq_of_le (show i ≤ j by omega) with hi' | rfl
      · exact (mem_Ub Fil e j c).1 hc i hi'
      · exact h
    · intro h
      exact h j (by omega)
  have hrange : LinearMap.range ψ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ := by
    apply le_antisymm
    · rintro _ ⟨⟨c, hc⟩, rfl⟩
      refine ⟨sumAt e j c, ?_, rfl⟩
      rw [sumAt_apply]
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (he m j)
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨c, hlow, hk⟩ := hS j w hw
      refine ⟨⟨c, (mem_Ub Fil e j c).2 hlow⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, sumAt_apply]
      exact hk
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hrange] at h1
  have : FiniteDimensional LL ↥(D ⊓ Fil (-j)) := Submodule.finiteDimensional_of_le inf_le_left
  let φ : ↥(D ⊓ Fil (-j)) →ₗ[LL] E ⧸ Fil (-j + 1) := (Fil (-j + 1)).mkQ ∘ₗ (D ⊓ Fil (-j)).subtype
  have hle' : D ⊓ Fil (-j + 1) ≤ D ⊓ Fil (-j) := inf_le_inf_left _ (hFa (by omega))
  have hφr : LinearMap.range φ = (D ⊓ Fil (-j)).map (Fil (-j + 1)).mkQ := by
    simp only [φ, LinearMap.range_comp, Submodule.range_subtype]
  have hφk : LinearMap.ker φ = (D ⊓ Fil (-j + 1)).comap (D ⊓ Fil (-j)).subtype := by
    ext ⟨x, hx⟩
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨(Submodule.mem_inf.1 hx).1, h⟩, fun h => h.2⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  rw [hφr, hφk, (Submodule.comapSubtypeEquivOfLe hle').finrank_eq] at h2
  omega

include hFa in

theorem indep_of_span (a₀ a₁ : ℤ) (h₀ : D ≤ Fil a₀) (h₁ : D ⊓ Fil a₁ = ⊥)
    (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hS : ∀ k : ℤ, ∀ w ∈ D ⊓ Fil (-k), ∃ c : Fin r → LL,
      (∀ j < k, ∑ m, c m • e m j ∈ Fil (-j + 1)) ∧ ∑ m, c m • e m k - w ∈ Fil (-k + 1))
    (hr : r ≤ finrank LL ↥D) (c : Fin r → LL) (hc : ∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) :
    c = 0 := by
  let H : ℤ → ℕ := fun j => finrank LL ↥(Ub Fil e j) + finrank LL ↥(D ⊓ Fil (-j + 1))
  have hstep : ∀ j, H (j + 1) = H j := by
    intro j
    have := count_step hFa D he hS j
    simp only [H]
    rw [show -(j + 1) + 1 = -j by ring]
    exact this
  have hiter : ∀ (j : ℤ) (N : ℕ), H (j + N) = H j := by
    intro j N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show j + ((N + 1 : ℕ) : ℤ) = (j + N) + 1 by push_cast; ring, hstep, ih]
  have hzero : ∀ m i, i < 1 - a₁ → e m i = 0 := by
    intro m i hi
    have h := he m i
    have h' : e m i ∈ D ⊓ Fil a₁ := ⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩
    rw [h₁] at h'
    exact (Submodule.mem_bot LL).1 h'
  have htop : Ub Fil e (1 - a₁) = ⊤ := by
    refine eq_top_iff.2 fun c _ => (mem_Ub Fil e _ c).2 fun i hi => ?_
    rw [Finset.sum_eq_zero fun m _ => by rw [hzero m i hi, smul_zero]]
    exact Submodule.zero_mem _
  have hUr : finrank LL ↥(Ub Fil e (1 - a₁)) = r := by
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have hH0 : H (1 - a₁) = r := by
    simp only [H]
    rw [show -(1 - a₁) + 1 = a₁ by ring, h₁, finrank_bot, hUr, add_zero]
  let N : ℕ := (a₁ - a₀).toNat
  have hJ : -((1 - a₁) + (N : ℤ)) + 1 ≤ a₀ := by
    have := Int.self_le_toNat (a₁ - a₀)
    omega
  have hD : D ⊓ Fil (-((1 - a₁) + (N : ℤ)) + 1) = D := inf_eq_left.2 (h₀.trans (hFa hJ))
  have hHJ := hiter (1 - a₁) N
  rw [hH0] at hHJ
  simp only [H] at hHJ
  rw [hD] at hHJ
  have hU : finrank LL ↥(Ub Fil e ((1 - a₁) + (N : ℤ))) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hU
  have hcU : c ∈ Ub Fil e ((1 - a₁) + (N : ℤ)) := (mem_Ub Fil e _ c).2 fun i _ => hc i
  rw [hU] at hcU
  exact (Submodule.mem_bot LL).1 hcU

include hFa in

theorem smulS_sub_cc {M : ℤ} {f : ℤ → E} (hf : LB M f) (hfF : ∀ k, f k ∈ Fil (-k))
    (g : PowerSeries LL) (j : ℤ) :
    smulS g f j - PowerSeries.constantCoeff g • f j ∈ Fil (-j + 1) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, j - M < (N + 1 : ℕ) :=
    ⟨(j - M).toNat, by have := Int.self_le_toNat (j - M); push_cast; omega⟩
  rw [smulS_eq_sum hf g j (N + 1) hN, Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact hFa (show -j + 1 ≤ -(j - ((i + 1 : ℕ) : ℤ)) by push_cast; omega) (hfF _)

include hFa in

theorem dvd_of_dg (a₁ : ℤ) (h₁ : D ⊓ Fil a₁ = ⊥) (he : ∀ m k, e m k ∈ D ⊓ Fil (-k))
    (hind : ∀ c : Fin r → LL, (∀ j, ∑ m, c m • e m j ∈ Fil (-j + 1)) → c = 0) :
    ∀ (k : ℕ) (g : Fin r → PowerSeries LL),
      (∀ j : ℤ, ∑ m, smulS (g m) (e m) j ∈ Fil ((k : ℤ) - j)) → ∀ m, PowerSeries.X ^ k ∣ g m := by
  have hLB : ∀ m, LB (1 - a₁) (e m) := by
    intro m i hi
    have h := he m i
    have h' : e m i ∈ D ⊓ Fil a₁ := ⟨(Submodule.mem_inf.1 h).1, hFa (by omega) (Submodule.mem_inf.1 h).2⟩
    rw [h₁] at h'
    exact (Submodule.mem_bot LL).1 h'
  have hF : ∀ m k, e m k ∈ Fil (-k) := fun m k => (Submodule.mem_inf.1 (he m k)).2
  intro k
  induction k with
  | zero => intro g _ m; simp
  | succ k ih =>
    intro g hg
    have hcc : (fun m => PowerSeries.constantCoeff (g m)) = 0 := by
      apply hind
      intro j
      have h1 : ∑ m, smulS (g m) (e m) j ∈ Fil (-j + 1) :=
        hFa (show -j + 1 ≤ ((k + 1 : ℕ) : ℤ) - j by push_cast; omega) (hg j)
      have h2 : ∑ m, (smulS (g m) (e m) j - PowerSeries.constantCoeff (g m) • e m j) ∈ Fil (-j + 1) :=
        Submodule.sum_mem _ fun m _ => smulS_sub_cc hFa (hLB m) (hF m) (g m) j
      have := Submodule.sub_mem _ h1 h2
      rwa [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun m _ => sub_sub_cancel _ _] at this
    have hX : ∀ m, PowerSeries.X ∣ g m := fun m =>
      (PowerSeries.X_dvd_iff).2 (congrFun hcc m)
    choose g' hg' using hX
    have hshift : ∀ m (j : ℤ), smulS (g m) (e m) (j + 1) = smulS (g' m) (e m) j := by
      intro m j
      rw [hg' m, smulS_mul (hLB m), show (PowerSeries.X : PowerSeries LL) = PowerSeries.X ^ 1 by
        rw [pow_one], smulS_X_pow (LB_smulS (hLB m) (g' m)) 1]
      simp
    have hg'd := ih g' fun j => by
      have := hg (j + 1)
      rw [Finset.sum_congr rfl fun m _ => hshift m j] at this
      rwa [show ((k + 1 : ℕ) : ℤ) - (j + 1) = (k : ℤ) - j by push_cast; ring] at this
    intro m
    rw [hg' m, pow_succ']
    exact mul_dvd_mul_left _ (hg'd m)

end Cnt

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
end
end

section
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [LocWach.Q, hs]

theorem q_mul : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
  funext i
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
    LocWach.q, W.q₀_def]

theorem cc_lev_pi (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π c ζ hζ
  have := congrArg PowerSeries.constantCoeff hE
  rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
  linear_combination this

theorem constantCoeff_q_zero_eq_p : PowerSeries.constantCoeff W.q₀ = (PD.p : O) := by
  have h := congrArg (PowerSeries.coeff 1) W.q₀_def
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  rw [h, map_sub, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
  have e : ((1 : PowerSeries O) + PowerSeries.X) ^ PD.p =
      (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one, add_comm]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]

theorem cc_lev_q_one (c : ZMod n) : PowerSeries.constantCoeff (W.lev c 1 W.q) = (PD.p : LL) := by
  have hq : W.q = (fun _ => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) W.q₀) * letπ +
      (PD.p : LetA O n) := by
    funext i
    simp only [LocWach.q, Pi.add_apply, Pi.mul_apply, letπ, Pi.natCast_apply]
    conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const W.q₀]
    rw [constantCoeff_q_zero_eq_p, map_natCast]
  rw [hq, map_add, map_mul, map_natCast, map_add, map_mul,
    cc_lev_pi W c 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self, mul_zero, zero_add,
    map_natCast]

theorem qroot_prim (hs : W.s = 1) (hp : (PD.p : LL) ≠ 0) {c : ZMod n} {ζ : LL}
    (h : Formalism.MainNotions.DeltaInvariantLattices.QRoot W c ζ) : IsPrimitiveRoot ζ PD.p := by
  obtain ⟨-, ⟨m, hm⟩, hcc⟩ := h
  rw [Q_eq_q W hs] at hcc
  have hpr : PD.p.Prime := PD.hp
  obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow hpr).1 (orderOf_dvd_of_pow_eq_one hm)
  have hprim : IsPrimitiveRoot ζ (PD.p ^ j) := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hp1 : ζ ^ PD.p = 1 := by
    by_contra hne
    exact Formalism.MainNotions.UnusedSlot80.LevR.cc_lev_q W c ζ ⟨j, hprim⟩ hne hcc
  have hdvd : PD.p ^ j ∣ PD.p ^ 1 := by rw [pow_one]; exact hprim.dvd_of_pow_eq_one _ hp1
  have hj1 : j ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hpr.one_lt).1 hdvd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj1 with rfl | rfl
  · rw [pow_zero] at hprim
    obtain rfl := IsPrimitiveRoot.one_right_iff.1 hprim
    exact absurd (cc_lev_q_one W c ▸ hcc) hp
  · rwa [pow_one] at hprim

theorem lev_q_eq (c : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) (hp : (PD.p : LL) ≠ 0) :
    ∃ u : PowerSeries LL, PowerSeries.constantCoeff u ≠ 0 ∧
      W.lev c ζ W.q = PowerSeries.X * u := by
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j) := ⟨1, by rwa [pow_one]⟩
  obtain ⟨E, hE0, hE', hE⟩ := W.lev_π c ζ hζ'
  have h := congrArg (W.lev c ζ) (q_mul W)
  rw [map_mul, map_sub, map_pow, map_add, map_one, hE, mul_pow, ← map_pow,
    hζ.pow_eq_one, map_one, one_mul] at h
  have hπ := cc_lev_pi W c ζ hζ'
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.2 (hζ.ne_one PD.hp.one_lt)
  have hE1 : PowerSeries.coeff 1 E = 1 := by
    have := PowerSeries.coeff_derivative E 0
    rw [hE'] at this
    simp only [Nat.cast_zero, zero_add, mul_one] at this
    rw [← this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0]
  have hpow : ∀ k : ℕ, PowerSeries.coeff 1 (E ^ k) = k := by
    intro k
    induction k with
    | zero => simp [PowerSeries.coeff_one]
    | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
        Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hE0, one_pow, hE1, ih]
      push_cast
      ring
  have hF0 : PowerSeries.constantCoeff (E ^ PD.p - 1) = 0 := by
    rw [map_sub, map_pow, hE0, one_pow, map_one, sub_self]
  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.2 hF0
  have hw0 : PowerSeries.constantCoeff w = (PD.p : LL) := by
    have h1 := congrArg (PowerSeries.coeff 1) hw
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub,
      hpow, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero] at h1
    exact h1.symm
  have hne : PowerSeries.constantCoeff (W.lev c ζ letπ) ≠ 0 := by rw [hπ]; exact hζ1
  refine ⟨(W.lev c ζ letπ)⁻¹ * w, ?_, ?_⟩
  · rw [map_mul, PowerSeries.constantCoeff_inv, hπ, hw0]
    exact mul_ne_zero (inv_ne_zero hζ1) hp
  · calc W.lev c ζ W.q = (W.lev c ζ letπ)⁻¹ * (W.lev c ζ letπ * W.lev c ζ W.q) := by
          rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hne, one_mul]
      _ = PowerSeries.X * ((W.lev c ζ letπ)⁻¹ * w) := by rw [h, hw]; ring

theorem letE_mul_self (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_smul_of_mem_Nl {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T}
    (hy : y ∈ W.Nl T c) : (letE c : LetA O n) • y = y := by
  obtain ⟨z, -, rfl⟩ := hy
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, letE_mul_self]

theorem Nl_le_N (T : LocLat G Qp LL O) (c : ZMod n) : W.Nl T c ≤ W.N T := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact (W.N T).smul_mem _ hz

theorem mem_Nl_of {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T} (hy : y ∈ W.N T)
    (hc : (letE c : LetA O n) • y = y) : y ∈ W.Nl T c :=
  ⟨y, hy, by simp only [LinearMap.smul_apply, LinearMap.id_apply]; exact hc⟩

theorem smul_eq_single {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T}
    (hc : (letE c : LetA O n) • y = y) (o : O) :
    o • y = (Pi.single c (PowerSeries.C o) : LetA O n) • y := by
  conv_lhs => rw [← hc]
  rw [← smul_assoc]
  congr 1
  funext i
  by_cases h : i = c
  · subst h; simp [letE, PowerSeries.smul_eq_C_mul]
  · simp [letE, h]

theorem letπ_mul_single (c : ZMod n) (a : PowerSeries O) :
    (letπ : LetA O n) * Pi.single c a = Pi.single c (PowerSeries.X * a) := by
  funext i
  by_cases h : i = c
  · subst h; simp [letπ]
  · simp [letπ, h]

theorem levN_sum {T : LocLat G Qp LL O} (c : ZMod n) (ζ : LL) {r : ℕ} {b : Fin r → W.DD T}
    (hbN : ∀ m, b m ∈ W.N T) (a : Fin r → LetA O n) (hy : ∑ m, a m • b m ∈ W.N T) (j : ℤ) :
    W.levN T c ζ ⟨∑ m, a m • b m, hy⟩ j =
      ∑ m, smulS (W.lev c ζ (a m)) (W.levN T c ζ ⟨b m, hbN m⟩) j := by
  have e : (⟨∑ m, a m • b m, hy⟩ : ↥(W.N T)) = ∑ m, a m • (⟨b m, hbN m⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp [Submodule.coe_sum])
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [W.levN_smul]
  rfl

theorem rank_le (hFr : IsFractionRing O LL) (T : LocLat G Qp LL O) (c : ZMod n) {r : ℕ}
    {b : Fin r → W.DD T} (hbS : ∀ j, b j ∈ W.Nl T c)
    (hu : ∀ x ∈ W.Nl T c, ∃! a : Fin r → PowerSeries O,
      x = ∑ j, (Pi.single c (a j) : LetA O n) • b j)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)] :
    r ≤ finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) := by
  have hbN : ∀ m, b m ∈ W.N T := fun m => Nl_le_N W T c (hbS m)
  let bN : Fin r → ↥(W.N T) := fun m => ⟨b m, hbN m⟩
  have hcmp : ∀ m, W.cmp T (bN m) ∈ DcrisL PD T.ρ (W.emb c) := by
    intro m
    have e : (letE c : LetA O n) • bN m = bN m :=
      Subtype.ext (letE_smul_of_mem_Nl W (hbS m))
    rw [← e]
    exact W.cmp_letter T c (bN m)
  let vv : Fin r → ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) := fun m =>
    ⟨ιV PD (LL := LL) (V := T.V) (W.cmp T (bN m)), Submodule.mem_map_of_mem (hcmp m)⟩
  have hli : LinearIndependent LL vv := by
    refine Fintype.linearIndependent_iff.2 fun g hg m => ?_
    have hg' : ιV PD (LL := LL) (V := T.V) (∑ m, g m • W.cmp T (bN m)) = 0 := by
      have := congrArg Subtype.val hg
      simpa [vv, Submodule.coe_sum, map_sum, map_smul] using this
    have hsum : ∑ m, g m • W.cmp T (bN m) = 0 :=
      Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (hg'.trans (map_zero _).symm)
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
      (Finset.univ : Finset (Fin r)) g
    choose o ho using fun i => hint i (Finset.mem_univ i)
    haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
    have hdne : algebraMap O LL d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hcz : W.cmp T (∑ i, o i • bN i) = 0 := by
      rw [map_sum]
      simp only [W.cmp_smul]
      calc ∑ i, algebraMap O LL (o i) • W.cmp T (bN i)
          = ∑ i, algebraMap O LL d • (g i • W.cmp T (bN i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ho i, Algebra.smul_def, mul_smul]
        _ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]
    obtain ⟨y, hy, hyz⟩ := h3.1 _ hcz
    set z : W.DD T := ∑ i, o i • b i with hz
    have hzc : ((∑ i, o i • bN i : ↥(W.N T)) : W.DD T) = z := by simp [hz, bN, Submodule.coe_sum]
    have hy' : (letπ : LetA O n) • y = z := by
      rw [← hzc, ← hyz]
      simp [Formalism.MainNotions.DeltaInvariantLattices.smulA]
    have hzl : z ∈ W.Nl T c := Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (hbS i)
    obtain ⟨a, ha, -⟩ := hu _ (mem_Nl_of W ((W.N T).smul_mem (letE c) hy) (by rw [smul_smul, letE_mul_self]))
    have rep1 : z = ∑ j, (Pi.single c (PowerSeries.C (o j)) : LetA O n) • b j := by
      rw [hz]
      exact Finset.sum_congr rfl fun j _ => smul_eq_single W (letE_smul_of_mem_Nl W (hbS j)) (o j)
    have rep2 : z = ∑ j, (Pi.single c (PowerSeries.X * a j) : LetA O n) • b j := by
      have e1 : z = (letE c : LetA O n) • z := (letE_smul_of_mem_Nl W hzl).symm
      rw [e1, ← hy', smul_comm, ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, letπ_mul_single]
    have heq := (hu z hzl).unique rep1 rep2
    have h0 : o m = 0 := by
      have := congrArg (fun f => PowerSeries.constantCoeff (f m)) heq
      simpa using this
    have : algebraMap O LL d * g m = 0 := by
      rw [← Algebra.smul_def, ← ho m, h0, map_zero]
    exact (mul_eq_zero.1 this).resolve_left hdne
  simpa using hli.fintype_card_le_finrank

end Loc

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
end
end
