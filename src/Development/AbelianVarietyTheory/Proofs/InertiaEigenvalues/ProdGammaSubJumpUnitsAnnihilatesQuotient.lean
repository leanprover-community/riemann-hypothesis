import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqStdPowerSeriesAtZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | exact GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamQ

theorem isUnit_one_add {O : Type} [CommRing O] (f : PowerSeries O)
    (hf : PowerSeries.constantCoeff f = 0) : IsUnit (1 + f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hf]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem gam_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  intro D HW F Cm l _ K s LL h W C u T hT k
  obtain ⟨χ, -, -, hγ₀, -, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨b, hb⟩ := ((GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s h.1).2.2.2.2.2.1 (χ W.gam)).2
  let U : AA K LL := fun _ => 1 + GlobalTheory.Cyc.XX l ↥(OL LL) s * b
  have hγQ : W.γA W.gam W.Q = W.Q * U := by
    funext i
    show W.γ₀ W.gam (W.Q i) = W.Q i * U i
    rw [hγ₀, hQ]
    exact hb
  have hUu : IsUnit U := Pi.isUnit_iff.2 fun _ => isUnit_one_add _ (by simp [GlobalTheory.Cyc.XX])
  have hγs : ∀ (a : AA K LL) (y : W.DD T), W.γ T (a • y) = W.γA W.gam a • W.γ T y := by
    intro a y
    have := W.γD_smul T W.gam (algebraMap (AA K LL) W.EE a) y
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  let v : AA K LL := ((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ)
  have hvU : v * U ^ k = 1 := by
    show (((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ) : AA K LL) * U ^ k = 1
    have e : U ^ k = ((hUu.unit ^ k : (AA K LL)ˣ) : AA K LL) := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [e, Units.inv_mul]
  have key : ∀ y : W.DD T, W.Q ^ k • W.γ T y = v • W.γ T (W.Q ^ k • y) := by
    intro y
    rw [hγs, map_pow, hγQ, mul_pow, smul_smul, mul_left_comm, hvU, mul_one]
  refine ⟨fun x hx => ?_, fun i ζ hζ => ?_⟩
  · rw [key]
    exact (W.N T).smul_mem v (W.N_Γ T W.gam _ hx)
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  have hlev := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩ hfull).1
  refine ⟨W.lev i ζ v, ?_, fun x hx hγ j => ?_⟩
  · have hg := W.gam_gen
    rw [(HW l).W_s] at hg
    have hΓ := ((Cm l).C K s LL h).tie.lev_Γ W.gam i ζ ζ s 1
      (by rw [(D.loc l).PD_p]; exact hζ) (by rw [Nat.cast_one]; exact hg.ge) (pow_one ζ).symm W.Q
    have hΓ' : W.lev i ζ W.Q * W.lev i ζ U = PowerSeries.rescale u (W.lev i ζ W.Q) := by
      rw [← map_mul, ← hγQ]; exact hΓ
    obtain ⟨w0, hw0, hQw⟩ := ((GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ).1
    rw [hQw, map_mul, PowerSeries.rescale_X] at hΓ'
    have h1 : w0 * W.lev i ζ U = PowerSeries.C u * PowerSeries.rescale u w0 := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ↥LL.1))
      linear_combination hΓ'
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul] at h2
    have hw0c : PowerSeries.constantCoeff w0 ≠ 0 := (hw0.map PowerSeries.constantCoeff).ne_zero
    have hUc : PowerSeries.constantCoeff (W.lev i ζ U) = u := by
      apply mul_left_cancel₀ hw0c
      rw [h2, mul_comm]
    have h3 := congrArg PowerSeries.constantCoeff (congrArg (W.lev i ζ) hvU)
    rw [map_mul, map_pow, map_one, map_mul, map_pow, map_one, hUc] at h3
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h3
  · have e1 : (⟨W.Q ^ k • W.γ T x, hγ⟩ : ↥(W.N T)) =
        v • (⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ : ↥(W.N T)) :=
      Subtype.ext (key x)
    have e2 : ex C h T i ζ ⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ =
        fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m :=
      funext fun m => GlobalTheory.NL.GradedLat.ex_gam C h T hT i ζ hζ.pow_eq_one ⟨W.Q ^ k • x, hx⟩ m
    rw [e1, hlev, e2]

end GlobalTheory.NL.GamQ
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_invQPow_gamma_stable : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  first | exact @GlobalTheory.NL.GamQ.gam_Q_pow | exact GlobalTheory.NL.GamQ.gam_Q_pow | (intros; apply GlobalTheory.NL.GamQ.gam_Q_pow <;> assumption)
end

section
open GlobalTheory.NL

namespace GlobalTheory.NL.Twist

variable {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]

theorem conv_mem_of_forall (w : PowerSeries L) (g : ℤ → M) (S : Submodule L M) (j : ℤ)
    (h : ∀ i : ℕ, g (j - i) ∈ S) : conv w g j ∈ S := by
  unfold conv
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem)
    (fun i => S.smul_mem _ (h i))

theorem conv_eq_sum (w : PowerSeries L) (g : ℤ → M) (m : ℤ) (hg : ∀ j < m, g j = 0) (k : ℤ) :
    conv w g k = ∑ i ∈ Finset.range ((k - m).toNat + 1), PowerSeries.coeff i w • g (k - i) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push_neg at hc
  apply hi
  have : g (k - i) = 0 := hg _ (by omega)
  simp [this]

theorem tri (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hSub : Monotone Sub) (y : ℕ)
    (f : ℤ → M) (hf : ∃ m : ℤ, ∀ j < m, f j = 0) (hfS : ∀ j, f j ∈ Sub j) (k : ℤ)
    (hk : ∀ j < k, f j ∈ Sub (j - y)) :
    (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧
    (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧
    (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧
    conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  obtain ⟨m, hm⟩ := hf
  have hg : ∀ j < m, (fun m => u ^ m • f m) j = 0 := fun j hj => by simp [hm j hj]
  refine ⟨⟨m, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · refine (Submodule.mem_bot L).1 (conv_mem_of_forall w _ ⊥ j (fun i => ?_))
    rw [hm _ (by omega), smul_zero]
    exact Submodule.zero_mem _
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) ≤ j) (hfS _)))
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) - y ≤ j - y) (hk _ (by omega))))
  · rw [conv_eq_sum w _ m hg k, Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 w • (u ^ (k - ((0 : ℕ) : ℤ)) • f (k - ((0 : ℕ) : ℤ))) -
        (PowerSeries.constantCoeff w * u ^ k) • f k = 0 := by
      simp [mul_smul]
    rw [add_sub_assoc, h0, add_zero]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
    exact hSub (by omega : k - ((i + 1 : ℕ) : ℤ) - y ≤ k - y) (hk _ (by omega))

end GlobalTheory.NL.Twist
end

section
open GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent : ∀ {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M] (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M), Monotone Sub → ∀ (y : ℕ) (f : ℤ → M), (∃ m : ℤ, ∀ j < m, f j = 0) → (∀ j, f j ∈ Sub j) → ∀ k : ℤ, (∀ j < k, f j ∈ Sub (j - y)) → (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧ (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧ (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧ conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  first | exact @GlobalTheory.NL.Twist.tri | exact GlobalTheory.NL.Twist.tri | (intros; apply GlobalTheory.NL.Twist.tri <;> assumption)
end

section
namespace GlobalTheory.NL.KillLevels

theorem kill {β α M R : Type} [DecidableEq β] [Semiring R] [AddCommMonoid M] [Module R M]
    (Sub : ℤ → Submodule R M) (y : ℕ) (S : α → Prop) (E : α → ℤ → M)
    (c : ℤ → β) (hc : Function.Injective c)
    (P : Finset β → α → α) (op : β → α → α)
    (hP0 : ∀ x, P ∅ x = x)
    (hP : ∀ A d x, d ∈ A → P A x = P (A.erase d) (op d x))
    (hS : ∀ d x, S x → S (op d x))
    (hE : ∀ x, S x → ∀ j, E x j ∈ Sub j)
    (hstep : ∀ d x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ j < k, E (op d x) j ∈ Sub (j - y)) ∧ (d = c k → E (op d x) k ∈ Sub (k - y))) :
    ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → ¬ Sub k' ≤ Sub (k' - y) → c k' ∈ A) → ∀ j, E (P A x) j ∈ Sub (j - y) := by
  have hins : ∀ A d x, d ∉ A → P (insert d A) x = P A (op d x) := fun A d x hd => by
    rw [hP (insert d A) d x (Finset.mem_insert_self d A), Finset.erase_insert hd]
  have pres : ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      S (P A x) ∧ ∀ j < k, E (P A x) j ∈ Sub (j - y) := by
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro x k hx hk
      rw [hP0]
      exact ⟨hx, hk⟩
    · intro d A hd ih x k hx hk
      rw [hins A d x hd]
      exact ih _ k (hS d x hx) (hstep d x k hx hk).1
  have nobad : ∀ A x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → Sub k' ≤ Sub (k' - y)) → ∀ j, E (P A x) j ∈ Sub (j - y) := by
    intro A x k hx hk hgood j
    obtain ⟨hS', hk'⟩ := pres A x k hx hk
    by_cases hj : j < k
    · exact hk' j hj
    · exact hgood j (not_lt.1 hj) (hE _ hS' j)
  suffices H : ∀ n : ℕ, ∀ A : Finset β, A.card ≤ n → ∀ x k, S x → (∀ j < k, E x j ∈ Sub (j - y)) →
      (∀ k', k ≤ k' → ¬ Sub k' ≤ Sub (k' - y) → c k' ∈ A) → ∀ j, E (P A x) j ∈ Sub (j - y) from
    fun A => H _ A le_rfl
  intro n
  induction n with
  | zero =>
    intro A hA x k hx hk hbad
    by_cases hex : ∃ k', k ≤ k' ∧ ¬ Sub k' ≤ Sub (k' - y)
    · obtain ⟨k', h1, h2⟩ := hex
      have h3 := hbad k' h1 h2
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hA)] at h3
      simp at h3
    · push Not at hex
      exact nobad A x k hx hk hex
  | succ n ih =>
    intro A hA x k hx hk hbad
    classical
    by_cases hex : ∃ m : ℕ, ¬ Sub (k + m) ≤ Sub (k + m - y)
    · have hm0 : ¬ Sub (k + (Nat.find hex : ℕ)) ≤ Sub (k + (Nat.find hex : ℕ) - y) := Nat.find_spec hex
      have hmin : ∀ m < Nat.find hex, Sub (k + m) ≤ Sub (k + m - y) :=
        fun m hm => not_not.1 (Nat.find_min hex hm)
      have hla : ∀ j < k + (Nat.find hex : ℕ), E x j ∈ Sub (j - y) := by
        intro j hj
        by_cases hjk : j < k
        · exact hk j hjk
        · have e : j = k + ((j - k).toNat : ℕ) := by omega
          have h1 := hmin (j - k).toNat (by omega)
          rw [← e] at h1
          exact h1 (hE x hx j)
      have hca : c (k + (Nat.find hex : ℕ)) ∈ A := hbad _ (by omega) hm0
      have hla' : ∀ j < k + (Nat.find hex : ℕ) + 1,
          E (op (c (k + (Nat.find hex : ℕ))) x) j ∈ Sub (j - y) := by
        intro j hj
        rcases lt_or_eq_of_le (Int.lt_add_one_iff.1 hj) with h | h
        · exact (hstep _ x _ hx hla).1 j h
        · rw [h]; exact (hstep _ x _ hx hla).2 rfl
      rw [hP A _ x hca]
      refine ih (A.erase _) ?_ _ _ (hS _ x hx) hla' ?_
      · have := Finset.card_erase_of_mem hca
        omega
      · intro k' hk' hb
        refine Finset.mem_erase.2 ⟨fun he => ?_, hbad k' (by omega) hb⟩
        have := hc he
        omega
    · push Not at hex
      refine nobad A x k hx hk fun k' hk' => ?_
      have h1 := hex (k' - k).toNat
      rwa [show k + (((k' - k).toNat : ℕ) : ℤ) = k' by omega] at h1

end GlobalTheory.NL.KillLevels

noncomputable section

namespace GlobalTheory.NL.KillLevels

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lev_algebraMap (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL) (d : O) :
    W.lev i ζ (algebraMap O (LetA O n) d) = PowerSeries.C (algebraMap O LL d) := by
  rw [AlgHom.commutes, PowerSeries.algebraMap_apply]

theorem map_sub_smul {M : Type} [AddCommGroup M] [Module LL M] (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (e : ↥(W.N T) →+ (ℤ → M))
    (he : ∀ (a : LetA O n) (x : ↥(W.N T)), e (a • x) = conv (W.lev i ζ a) (e x))
    (y : ℕ) (z : W.DD T) (d : O) (hz : W.Q ^ y • z ∈ W.N T) (hγz : W.Q ^ y • W.γ T z ∈ W.N T) :
    ∃ hz' : W.Q ^ y • (W.γ T z - d • z) ∈ W.N T, ∀ j : ℤ,
      e ⟨_, hz'⟩ j = e ⟨_, hγz⟩ j - algebraMap O LL d • e ⟨_, hz⟩ j := by
  have hdz : W.Q ^ y • (d • z) = algebraMap O (LetA O n) d • (W.Q ^ y • z) := by
    rw [← algebraMap_smul (LetA O n) d z, smul_smul, mul_comm, ← smul_smul]
  have hz' : W.Q ^ y • (W.γ T z - d • z) ∈ W.N T := by
    rw [smul_sub, hdz]
    exact (W.N T).sub_mem hγz ((W.N T).smul_mem _ hz)
  refine ⟨hz', fun j => ?_⟩
  have e1 : (⟨_, hz'⟩ : ↥(W.N T)) = ⟨_, hγz⟩ - algebraMap O (LetA O n) d • ⟨_, hz⟩ := by
    apply Subtype.ext
    show W.Q ^ y • (W.γ T z - d • z) = W.Q ^ y • W.γ T z - algebraMap O (LetA O n) d • (W.Q ^ y • z)
    rw [smul_sub, hdz]
  rw [e1, map_sub, he, lev_algebraMap, GlobalTheory.NL.LevInj.conv_C]
  rfl

theorem aeval_erase [DecidableEq Oˣ] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (A : Finset Oˣ) (d : Oˣ)
    (z : W.DD T) (hd : d ∈ A) :
    Polynomial.aeval (W.γ T) (∏ c ∈ A, ((Polynomial.X : Polynomial O) - Polynomial.C (Units.val c))) z =
      Polynomial.aeval (W.γ T) (∏ c ∈ A.erase d, ((Polynomial.X : Polynomial O) - Polynomial.C (Units.val c)))
        (W.γ T z - (d : O) • z) := by
  rw [← Finset.prod_erase_mul A _ hd, map_mul, Module.End.mul_apply]
  congr 1
  simp

theorem algebraMap_uU_zpow (W : LocWach PD LL O v n) (m : ℤ) :
    algebraMap O LL ((uU W ^ m : Oˣ) : O) = algebraMap O LL (W.χΓ W.gam : O) ^ m := by
  have h2 := congrArg Units.val (map_zpow (Units.map (algebraMap O LL).toMonoidHom) (uU W) m)
  rw [Units.val_zpow_eq_zpow_val] at h2
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h2
  exact h2

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}

open Classical in

def Ex (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) : ℤ → T.V ⊗[ℚ_[l]] P.R.B :=
  if hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T then ex C h T i ζ ⟨_, hz⟩ else 0

theorem Ex_eq (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T) :
    Ex C h T i ζ y z = ex C h T i ζ ⟨_, hz⟩ := by
  unfold Ex
  rw [dif_pos hz]

def SubF (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (k : ℤ) :
    Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) :=
  Di H h T i ⊓ (FilAt (P.PD K) T τ (-k)).comap (ιV (P.PD K) (LL := ↥LL.1) (V := T.V))

theorem SubF_mono (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Monotone (SubF H h T i τ) := by
  intro a b hab
  have hanti : Antitone (FilAt (P.PD K) T τ) :=
    antitone_int_of_succ_le (GlobalTheory.NL.Model.FilAt_anti T τ)
  exact inf_le_inf_left _ (Submodule.comap_mono (hanti (by omega)))

set_option maxHeartbeats 1000000 in

theorem exists_jump (H : LocHW l P) (h : Good K s LL) (T : Lt K LL) (i : Let K)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : ℕ) (k : ℤ) (hb : ¬ SubF H h T i τ k ≤ SubF H h T i τ (k - y)) :
    ∃ a : ℤ, IsJumpV (P.PD K) T.ρ τ a ∧ -k ≤ a ∧ a ≤ y - k - 1 := by
  by_contra hn
  push Not at hn
  apply hb
  have hnj : ∀ a : ℤ, -k ≤ a → a ≤ y - k - 1 →
      FildR (P.PD K) T.ρ τ (a + 1) = FildR (P.PD K) T.ρ τ a := by
    intro a h1 h2
    by_contra hj
    exact absurd h2 (not_le.2 (hn a hj h1))
  have hfil : ∀ m : ℕ, m ≤ y → FildR (P.PD K) T.ρ τ (-k + m) = FildR (P.PD K) T.ρ τ (-k) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [show -k + ((m + 1 : ℕ) : ℤ) = (-k + m) + 1 by push_cast; ring,
        hnj _ (by omega) (by omega), ih (by omega)]
  have hF : FilAt (P.PD K) T τ (-(k - y)) = FilAt (P.PD K) T τ (-k) := by
    unfold FilAt
    rw [show -(k - (y : ℤ)) = -k + (y : ℕ) by ring, hfil y le_rfl]
  intro e he
  unfold SubF at he ⊢
  rw [hF]
  exact he

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem Ex_sub_smul (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1) (y : ℕ)
    (z : (H.W K s LL h).DD T) (d : ↥(OL LL))
    (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
    (hγz : (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T) (j : ℤ) :
    Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j =
      Ex C h T i ζ y ((H.W K s LL h).γ T z) j - algebraMap ↥(OL LL) ↥LL.1 d • Ex C h T i ζ y z j := by
  obtain ⟨hz', he⟩ := map_sub_smul (H.W K s LL h) T i ζ ((C.C K s LL h).tie.levB T i ζ)
    (GlobalTheory.NL.Model.ex_smul C h T i ζ) y z d hz hγz
  rw [Ex_eq C h T i ζ y _ hz', Ex_eq C h T i ζ y _ hγz, Ex_eq C h T i ζ y z hz]
  exact he j

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem step (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL) (i : Let K) (ζ : ↥LL.1)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (y : ℕ) (w : PowerSeries ↥LL.1)
    (hw0 : PowerSeries.constantCoeff w = algebraMap ↥(OL LL) ↥LL.1
      ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (-(y : ℤ)))
    (hγN : ∀ z : (H.W K s LL h).DD T, (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T →
      (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T)
    (hw : ∀ (z : (H.W K s LL h).DD T) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
      (hγ : (H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z ∈ (H.W K s LL h).N T) (j : ℤ),
      ex C h T i ζ ⟨(H.W K s LL h).Q ^ y • (H.W K s LL h).γ T z, hγ⟩ j =
        conv w (fun m => algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ m •
          ex C h T i ζ ⟨(H.W K s LL h).Q ^ y • z, hz⟩ m) j)
    (hE : ∀ z : (H.W K s LL h).DD T, (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T →
      ∀ j, Ex C h T i ζ y z j ∈ SubF H h T i τ j)
    (d : ↥(OL LL)) (z : (H.W K s LL h).DD T) (k : ℤ) (hz : (H.W K s LL h).Q ^ y • z ∈ (H.W K s LL h).N T)
    (hk : ∀ j < k, Ex C h T i ζ y z j ∈ SubF H h T i τ (j - y)) :
    (∀ j < k, Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j ∈ SubF H h T i τ (j - y)) ∧
      (algebraMap ↥(OL LL) ↥LL.1 d =
          algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (k - y) →
        Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) k ∈ SubF H h T i τ (k - y)) := by
  have hform : ∀ j, Ex C h T i ζ y ((H.W K s LL h).γ T z - d • z) j =
      conv w (fun m => algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ m •
        Ex C h T i ζ y z m) j - algebraMap ↥(OL LL) ↥LL.1 d • Ex C h T i ζ y z j := by
    intro j
    rw [Ex_sub_smul C h T i ζ y z d hz (hγN z hz) j, Ex_eq C h T i ζ y _ (hγN z hz),
      Ex_eq C h T i ζ y z hz, hw z hz (hγN z hz) j]
  have hbdd : ∃ m : ℤ, ∀ j < m, Ex C h T i ζ y z j = 0 := by
    obtain ⟨m, hm⟩ := (C.C K s LL h).tie.levB_supp T i ζ ⟨_, hz⟩
    exact ⟨m, fun j hj => by rw [Ex_eq C h T i ζ y z hz]; exact hm j hj⟩
  obtain ⟨-, -, h3, h4⟩ := GlobalTheory.T.powerSeriesTwistedScaling_triangular_laurent w
    (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)))
    (SubF H h T i τ) (SubF_mono H h T i τ) y (Ex C h T i ζ y z) hbdd (hE z hz) k hk
  refine ⟨fun j hj => ?_, fun hd => ?_⟩
  · rw [hform j]
    exact (SubF H h T i τ _).sub_mem (h3 j hj) ((SubF H h T i τ _).smul_mem _ (hk j hj))
  · rw [hform k, hd]
    have hu0 : algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ≠ 0 :=
      (((H.W K s LL h).χΓ (H.W K s LL h).gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
    have e : algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ (k - (y : ℤ)) =
        PowerSeries.constantCoeff w *
          algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL)) ^ k := by
      rw [hw0, ← zpow_add₀ hu0, neg_add_eq_sub]
    rw [e]
    exact h4

end Concrete

end GlobalTheory.NL.KillLevels

end

namespace GlobalTheory.NL.KillLevels

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem annihilate : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ Fs : Finset (↥(OL LL))ˣ, (∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → uU W ^ (-(a + j)) ∈ Fs) → ∀ x ∈ invN W T (W.Q ^ y), Polynomial.aeval (W.γ T) (∏ c ∈ Fs, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x ∈ W.N T := by
  classical
  intro D HW F Cm l _ K s LL h W T hT y hy Fs hFs x hx
  have hx' : W.Q ^ y • x ∈ W.N T := by simpa [invN, smulA] using hx
  obtain ⟨hγ, hgam⟩ := GlobalTheory.T.wachN_invQPow_gamma_stable D HW F Cm l K s LL h T hT y
  let S : W.DD T → Prop := fun z => W.Q ^ y • z ∈ W.N T
  let op : (↥(OL LL))ˣ → W.DD T → W.DD T := fun d z => W.γ T z - (d : ↥(OL LL)) • z
  let Pf : Finset (↥(OL LL))ˣ → W.DD T → W.DD T := fun A z =>
    Polynomial.aeval (W.γ T) (∏ c ∈ A, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) z
  have hP0 : ∀ z, Pf ∅ z = z := by intro z; simp [Pf]
  have hP : ∀ A d z, d ∈ A → Pf A z = Pf (A.erase d) (op d z) := fun A d z hd => aeval_erase W T A d z hd
  have hS : ∀ d z, S z → S (op d z) := fun d z hz =>
    (map_sub_smul W T 0 1 (((Cm l).C K s LL h).tie.levB T 0 1)
      (GlobalTheory.NL.Model.ex_smul (Cm l) h T 0 1) y z (d : ↥(OL LL)) hz (hγ z hz)).1
  have hSA : ∀ A z, S z → S (Pf A z) := by
    intro A
    refine Finset.induction_on A ?_ ?_
    · intro z hz; rw [hP0]; exact hz
    · intro d A hd ih z hz
      rw [hP (insert d A) d z (Finset.mem_insert_self d A), Finset.erase_insert hd]
      exact ih _ (hS d z hz)
  have hQ : S (Pf Fs x) := hSA Fs x hx'
  refine (GlobalTheory.T.mem_wachN_iff_expansion D HW F Cm l K s LL h T hT y (Pf Fs x) hQ).2 ?_
  intro i ζ hζ
  obtain ⟨τ, hτ⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).1 i ζ hζ
  obtain ⟨w, hw0, hw⟩ := hgam i ζ hζ
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hτ
  let c : ℤ → (↥(OL LL))ˣ := fun k => uU W ^ (k - (y : ℤ))
  have hu0 : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ≠ 0 :=
    ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hc : Function.Injective c := by
    intro a b hab
    by_contra hne
    have h1 : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ^ (a - (y : ℤ)) =
        algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) ^ (b - (y : ℤ)) :=
      (algebraMap_uU_zpow W _).symm.trans
        ((congrArg (fun e : (↥(OL LL))ˣ => algebraMap ↥(OL LL) ↥LL.1 (e : ↥(OL LL))) hab).trans
          (algebraMap_uU_zpow W _))
    refine GlobalTheory.NL.AtZero.chi_gam_zpow_ne_one W (a - b) (sub_ne_zero.2 hne) ?_
    have e : a - b = (a - (y : ℤ)) - (b - (y : ℤ)) := by ring
    rw [e, zpow_sub₀ hu0, h1, div_self (zpow_ne_zero _ hu0)]
  have hE : ∀ z, S z → ∀ j, Ex (Cm l) h T i ζ y z j ∈ SubF (HW l) h T i τ j := by
    intro z hz j
    rw [Ex_eq (Cm l) h T i ζ y z hz]
    exact ((hlat _).1 (GlobalTheory.NL.Model.ex_mem_Lat (Cm l) h T i ζ ⟨_, hz⟩)).2 j
  have hbdd : ∀ z, S z → ∃ m : ℤ, ∀ k < m, Ex (Cm l) h T i ζ y z k = 0 := by
    intro z hz
    rw [Ex_eq (Cm l) h T i ζ y z hz]
    exact ((Cm l).C K s LL h).tie.levB_supp T i ζ ⟨_, hz⟩
  obtain ⟨m, hm⟩ := hbdd x hx'
  have key := kill (SubF (HW l) h T i τ) y S (Ex (Cm l) h T i ζ y) c hc Pf op hP0 hP hS hE
    (fun d z k hz hk =>
      ⟨(step (Cm l) h T i ζ τ y w hw0 hγ hw hE (d : ↥(OL LL)) z k hz hk).1, fun hd =>
        (step (Cm l) h T i ζ τ y w hw0 hγ hw hE (d : ↥(OL LL)) z k hz hk).2
          (by rw [hd]; exact algebraMap_uU_zpow W _)⟩)
    Fs x m hx' (fun j hj => by rw [hm j hj]; exact Submodule.zero_mem _)
    (fun k _ hb => by
      obtain ⟨a, ha, h1, h2⟩ := exists_jump (HW l) h T i τ y k hb
      have h3 := hFs a ⟨τ, ha⟩ ((y : ℤ) - k - a).toNat (by omega) (by omega)
      have e : -(a + ((((y : ℤ) - k - a).toNat : ℕ) : ℤ)) = k - (y : ℤ) := by omega
      rw [e] at h3
      exact h3)
  obtain ⟨m', hm'⟩ := hbdd _ hQ
  refine ⟨fun j => Ex (Cm l) h T i ζ y (Pf Fs x) (j + y), (hlat _).2 ⟨⟨m' - y, fun k hk => hm' _ (by omega)⟩,
    fun k => ?_⟩, fun j => ?_⟩
  · have h1 := key (k + y)
    rw [add_sub_cancel_right] at h1
    exact h1
  · show _ = Ex (Cm l) h T i ζ y (Pf Fs x) (j - y + y)
    rw [sub_add_cancel, Ex_eq (Cm l) h T i ζ y _ hQ]

end GlobalTheory.NL.KillLevels
end
