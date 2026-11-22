module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CrystallineToDeRhamInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisCmp

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem cf_sub_level_kernel_detection {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (f g : Amb LL Ks D) (i : ℤ) : cf (f - g) i = cf f i - cf g i := by
  simp [cf]

theorem constSeries_add {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d d' : D) : cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

theorem constSeries_sum {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    {q : ℕ} (d : Fin q → D) : cstD (LL := LL) Ks (∑ k, d k) = ∑ k, cstD Ks (d k) := by
  classical
  induction (Finset.univ : Finset (Fin q)) using Finset.induction_on with
  | empty => simp [cstD]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, constSeries_add, ih]

theorem constSeries_C_smul {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (r : LL) (d : D) :
    HahnSeries.ofPowerSeries ℤ Ks (PowerSeries.C (algebraMap LL Ks r)) • cstD (LL := LL) Ks d =
      cstD Ks (r • d) := by
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnModule.single_zero_smul_eq_smul]
  simp only [cstD]
  rw [← HahnModule.of_smul]
  congr 1
  ext j
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · rw [algebraMap_smul, TensorProduct.tmul_smul]
  · rw [smul_zero]

theorem coeff_constSeries {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d : D) (i : ℤ) : cf (cstD (LL := LL) Ks d) i = if i = 0 then (1 : Ks) ⊗ₜ[LL] d else 0 := by
  simp [cf, cstD, HahnSeries.coeff_single]

theorem Q_eq_unit_mul_qP (hs1 : W.s = 1)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) :
    ∃ u : (LetA O n)ˣ, W.Q = (u : LetA O n) * qP W := by
  obtain ⟨u, hu⟩ := hp9.2.2.2.2.1
  refine ⟨u, ?_⟩
  have hQq : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    rw [hs1, Nat.sub_self, pow_zero]
    rfl
  rw [hQq, hu]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP]

theorem constantCoeff_pi0_eq_zero_of_p9ring
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (j : ZMod n) : PowerSeries.constantCoeff (W.π₀ j) = 0 := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  rw [hw]
  simp [letπ, zero_pow hp1]

end Formalism.MainNotions.N.Ln03.Pf
