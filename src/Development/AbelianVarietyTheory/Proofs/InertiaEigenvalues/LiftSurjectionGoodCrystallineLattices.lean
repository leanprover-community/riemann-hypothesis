import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentMonodromyImageValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulDescentPhiMemLatticeOfOrbitBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemTameDescentClassEqOfPowMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.WDivE

theorem coeff_vanish_mul {K : Type} [CommRing K] {F G : K⟦X⟧} {a b : ℕ}
    (hF : ∀ k, a < k → coeff k F = 0) (hG : ∀ k, b < k → coeff k G = 0) (k : ℕ) (hk : a + b < k) :
    coeff k (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : a < p.1
  · rw [hF _ h, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem eq_sum_of_vanish {K : Type} [CommRing K] {P : K⟦X⟧} {N : ℕ}
    (hP : ∀ k, N ≤ k → coeff k P = 0) : P = ∑ k : Fin N, C (coeff (k : ℕ) P) * X ^ (k : ℕ) := by
  ext m
  rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega), Finset.sum_eq_zero]
    intro b _; rw [if_neg]; omega

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [CompleteSpace K] [NeZero e] in
theorem quotE_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : quotE l e f ∈ A O K := fun n => by
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)

theorem div_E_step {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e * g :=
  ⟨f - E K l e * quotE l e f, quotE l e f,
    sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)),
    fun k hk => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m,
    quotE_mem_A l e hf, by ring⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem coeff_E_pow_vanish (n : ℕ) : ∀ k, e * n < k → coeff k (E K l e ^ n) = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_one]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ]
    refine coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)
    rw [E, map_add, coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem div_E_pow (n : ℕ) {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e * n ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e ^ n * g := by
  induction n with
  | zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩
  | succ n ih =>
    obtain ⟨P, g, hP, hPv, hg, rfl⟩ := ih
    obtain ⟨Q, h, hQ, hQv, hh, rfl⟩ := div_E_step l e hg
    refine ⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ),
      fun k hk => ?_, hh, by ring⟩
    have he := NeZero.pos e
    rw [map_add, hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]
    exact coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1)
      (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)

end GlobalTheory.WDivE

theorem GlobalTheory.weierstrassDiv_E_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  intro O K _ _ _ _ _ _ l e _ _ _ n f hf
  obtain ⟨P, g, hP, hPv, hg, rfl⟩ := GlobalTheory.WDivE.div_E_pow l e n hf
  choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)
  refine ⟨c, g, hg, ?_⟩
  simp only [hc]
  rw [← GlobalTheory.WDivE.eq_sum_of_vanish hPv]
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_eisensteinPow_integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  atlas_forward_decl GlobalTheory.weierstrassDiv_E_pow
end

section
section
open PowerSeries GlobalTheory.BK
open scoped NormedField Valued

noncomputable section

namespace GlobalTheory.ZFin

theorem isDomain_isPrincipalIdealRing (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] : IsDomain O ∧ IsPrincipalIdealRing O := by
  have hl : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact_mod_cast Padic.norm_p_lt_one
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  letI : NontriviallyNormedField K :=
    { ‹NormedField K› with
      non_trivial := ⟨(l : K)⁻¹, by
        rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.2 hl0) |>.2 hl⟩ }
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  haveI : CompactSpace 𝒪[K] := by
    have h1 : ((𝒪[K] : Set K)) = Metric.closedBall 0 1 := by
      ext x; simp [Valued.integer.mem_iff]
    have h2 : IsCompact ((𝒪[K] : Set K)) := h1 ▸ isCompact_closedBall 0 1
    exact (isCompact_iff_compactSpace (s := (𝒪[K] : Set K))).1 h2
  haveI : IsPrincipalIdealRing 𝒪[K] := Valued.integer.isPrincipalIdealRing_of_compactSpace
  let f : O →+* 𝒪[K] :=
    { toFun := fun x => ⟨algebraMap O K x, Valued.integer.mem_iff.2 ((IsUnitBall.mem_range_iff _).1 ⟨x, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => IsUnitBall.inj (O := O) (K := K) (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (IsUnitBall.mem_range_iff (O := O) (y : K)).2 (Valued.integer.mem_iff.1 y.2)
    exact ⟨x, Subtype.ext hx⟩
  let g := RingEquiv.ofBijective f hf
  haveI : IsDomain O := (IsUnitBall.inj (O := O) (K := K)).isDomain (algebraMap O K)
  exact ⟨inferInstance, IsPrincipalIdealRing.of_surjective (g.symm : 𝒪[K] →+* O) g.symm.surjective⟩

theorem exists_eq_add_E_pow_mul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (n : ℕ) (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧
      f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g :=
  GlobalTheory.T.weierstrass_division_eisensteinPow_integral O K l e n f hf

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

variable (K l e a ι) in

def gen (η : ℕ) (p : ZMod a × ι × Fin (e * η)) : Vec K a ι :=
  Pi.single p.1 (Pi.single p.2.1 (Ezpow K l e (-η) * X ^ (p.2.2 : ℕ)))

theorem gen_mem (P : PhiMod O K l e a ι) (η : ℕ) (p : ZMod a × ι × Fin (e * η)) :
    gen K l e a ι η p ∈ P.EM η := by
  rw [mem_divE]
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, gen]
  by_cases hτ : τ = p.1
  · subst hτ
    rw [Pi.single_eq_same]
    by_cases hi : i = p.2.1
    · subst hi
      rw [Pi.single_eq_same, ← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
      exact pow_mem HasU.X_mem _
    · rw [Pi.single_eq_of_ne hi, mul_zero]; exact zero_mem _
  · rw [Pi.single_eq_of_ne hτ]; simp

theorem sum_gen_apply (η : ℕ) (c : ZMod a × ι × Fin (e * η) → O) (τ : ZMod a) (i : ι) :
    (∑ p, c p • gen K l e a ι η p) τ i =
      Ezpow K l e (-η) * ∑ k : Fin (e * η), C (algebraMap O K (c (τ, i, k))) * X ^ (k : ℕ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, gen, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [Pi.single_apply, ite_apply, Pi.zero_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx]), Fintype.sum_eq_single i
    (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K⟦X⟧ (c (τ, i, k)), algebraMap_eq_C, smul_eq_mul, mul_left_comm]

theorem finite_quot (P : PhiMod O K l e a ι) (η : ℕ) :
    Module.Finite O ((P.EM η).restrictScalars O ⧸
      (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) := by
  let F : (ZMod a × ι × Fin (e * η) → O) →ₗ[O] (P.EM η).restrictScalars O :=
    LinearMap.codRestrict _ (Fintype.linearCombination O (gen K l e a ι η)) fun c => by
      rw [Fintype.linearCombination_apply]
      exact sum_mem fun p _ => Submodule.smul_mem _ _ (gen_mem P η p)
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp F) fun q => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hy2 : E K l e ^ η • y ∈ P.M := hy
  have hyA (τ : ZMod a) (i : ι) : E K l e ^ η * y τ i ∈ A O K := by
    have := mem_vecs.1 (mem_tot.1 hy2 τ) i
    simpa using this
  choose c g hg hfg using fun τ i => exists_eq_add_E_pow_mul O K l e η _ (hyA τ i)
  refine ⟨fun p => c p.1 p.2.1 p.2.2, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (∑ p, c p.1 p.2.1 p.2.2 • gen K l e a ι η p) - y ∈ P.M
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  rw [Pi.sub_apply, Pi.sub_apply, sum_gen_apply]
  have hy' : y τ i = Ezpow K l e (-η) * (E K l e ^ η * y τ i) := by
    rw [← mul_assoc, mul_comm (Ezpow K l e (-η)), E_pow_mul_Ezpow_neg, one_mul]
  dsimp only
  rw [hy', hfg τ i, mul_add, sub_add_cancel_left, ← mul_assoc,
    mul_comm (Ezpow K l e (-η)) (E K l e ^ η), E_pow_mul_Ezpow_neg, one_mul]
  exact neg_mem (hg τ i)

variable [TameDescentExponentData K l e a]

theorem finite_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Finite O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_quot D.toPhiMod η
  exact Module.Finite.equiv (D.desc.quotInvEquiv η)

theorem free_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Free O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_Z D
  haveI : NoZeroSMulDivisors O D.Z := ⟨fun {c w} h => by
    have h1 : c • (w : D.Pol) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul K c] at h1
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (IsUnitBall.inj (O := O) (K := K) (by rw [h2, map_zero]))
    · exact Or.inr (Subtype.ext h2)⟩
  exact Module.free_of_finite_type_torsion_free'

theorem exists_pow_smul_mem_range {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.PolEta η ↔
      ∃ n : ℕ, (l : K) ^ n • w ∈ LinearMap.range (Descent.quotToPol D.toPhiMod η) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := mem_vecs.1 (mem_tot.1 hy τ) i
      simpa using this⟩
    obtain ⟨v, hv, hd⟩ := D.exists_sub_hatTot_mem_Mhat η ((D.smul_hatTot_mem_Mhat_iff η hy').2 hy)
    have hv' : v ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := invL_A_le_Rpi l e (mem_vecs.1 (mem_tot.1 hv τ) i)
      simpa using this⟩
    have hcls := (D.hatTot_sub_mem_Mhat_iff hy' hv').1 hd
    have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
      simp [smul_eq_C_mul]
    choose n hn using fun p : ZMod a × ι => mem_tot.1 hv p.1 p.2
    refine ⟨Finset.univ.sup n, Submodule.Quotient.mk ⟨(l : K) ^ Finset.univ.sup n • v, ?_⟩, ?_⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
      rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
      exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
    · change D.cls ((l : K) ^ Finset.univ.sup n • v) = (l : K) ^ Finset.univ.sup n • D.cls y
      rw [map_smul, hcls]
  · rintro ⟨n, q, hq⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : (l : K) ^ n • w ∈ D.PolEta η := by
      rw [← hq]
      exact D.cls_mem_PolEta hy
    have h2 := (D.PolEta η).smul_mem ((l : K) ^ n)⁻¹ h1
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

theorem mem_Zl_iff {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.Zl ↔ ∃ n : ℕ, (l : K) ^ n • w ∈ D.Z := by
  constructor
  · rintro ⟨hw1, hw2⟩
    obtain ⟨n, q, hq⟩ := (exists_pow_smul_mem_range D w).1 hw1
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨n, D.desc.mem_Z.2 ⟨⟨y, hy, hq⟩, fun g => ?_⟩⟩
    rw [map_smul, hw2 g]
  · rintro ⟨n, hn⟩
    have h2 := D.Zl.smul_mem ((l : K) ^ n)⁻¹ (D.desc.mem_Zl_of_mem_Z hn)
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

end GlobalTheory.ZFin

open GlobalTheory.ZFin in

theorem GlobalTheory.ZFin.finiteFree_and_localisation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨⟨free_Z D, finite_Z D⟩, Descent.quotToPol_injective (P := D.toPhiMod) η,
    fun w => exists_pow_smul_mem_range D w, D.desc.map_invariants_actQuot η, fun w => mem_Zl_iff D w⟩
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  atlas_forward_decl GlobalTheory.ZFin.finiteFree_and_localisation
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK.MonIntegral

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

omit [CompleteSpace K] in
theorem pow_smul_mem (W : Submodule O D.Pol) (n : ℕ) {w : D.Pol} (hw : w ∈ W) : (l : K) ^ n • w ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hw _

omit [CompleteSpace K] [NeZero e] in

theorem E_smul_mem_EM {p : Vec K a ι} (hp : p ∈ D.L) : E K l e • p ∈ D.EM η := by
  rw [mem_divE, smul_comm]
  exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)

omit [CompleteSpace K] in

theorem cls_E_smul_eq_zero {f : Vec K a ι} (hf : Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) :
    D.cls (E K l e • f) = 0 := by
  have h := D.smul_mem_Man (pow_mem (E_mem l e (Rpi O K l e)) (2 * H + 1)) hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  rw [smul_smul, pow_succ', mul_assoc, h1, mul_one] at h
  exact D.cls_eq_zero_iff.2 h

end GlobalTheory.BK.MonIntegral

open GlobalTheory.BK.MonIntegral in

theorem GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hH h14 h10 r hr hc hrl hl y hy m hm
  obtain ⟨hsplit, hfil, -⟩ := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hH h10
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hH h10
  have hyY : y ∈ D.Y := D.desc.Y'_le_Y η hy
  set W : Submodule O D.Pol :=
    ((D.EM η).restrictScalars O).map (D.cls.restrictScalars O) with hW
  have hL : ∀ p ∈ D.L, D.cls (E K l e • p) ∈ W := fun p hp => ⟨_, E_smul_mem_EM D hp, rfl⟩
  have hMM : ∀ μ ∈ D.MM, D.cls (E K l e • μ) ∈ W := fun μ hμ => by
    obtain ⟨p, hp, f, hf, rfl⟩ := hsplit μ hμ
    rw [smul_add, map_add, cls_E_smul_eq_zero D (hfil f hf), add_zero]
    exact hL p hp
  have h1 : D.Mon y ∈ W := by
    rw [D.Mon_eq]
    refine sub_mem (hint _ (D.desc.cls_mem_Z hyY)).1 ?_
    obtain ⟨p, hp, f, hf, h⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη hH h14 y hy
    rw [h, smul_add, map_add, smul_comm (E K l e) _ p, smul_comm (E K l e) _ f,
      D.cls.map_smul ((l : K) ^ _), D.cls.map_smul (_⁻¹ : K), cls_E_smul_eq_zero D (hfil f hf), smul_zero, add_zero]
    exact pow_smul_mem D W _ (hL p hp)
  have h2 : (l : K) ^ (η * (r + 1)) • D.Mon (D.phi m) ∈ W := by
    rw [D.Mon_eq, smul_sub, BKDat.Lc_cls, PhiMod.EN_apply]
    refine sub_mem (pow_smul_mem D W _ (hMM _ (D.conn_mem_MM
      (D.ext_mono (A_le_S l e) (D.phi_mem_L hm.1))))) ?_
    rw [← map_smul, ← smul_comm (E K l e)]
    exact hMM _ (GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D r hr hc hrl hl m hm)
  refine ⟨?_, ?_⟩
  · rw [map_add, smul_add]
    exact add_mem (pow_smul_mem D W _ h1) h2
  · refine D.desc.actPol.invariants.smul_mem _ (D.desc.Mon_mem_invariants (add_mem hyY.2 fun g => ?_))
    rw [D.desc.act_phi, hm.2 g]
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDescent_pow_smul_monodromy_add_phi_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  atlas_forward_decl GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.LiftImage

theorem lift_image : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : BKHom D₀ D₁) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D₁ U → ∀ ω : D₁.Pol, (∃ w ∈ D₁.Zl, D₁.Lc w = ω) → ∀ c : ℕ, (∃ w₀ ∈ D₀.Zl, F.onPol w₀ = (l : K) ^ c • ω) → ∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = ω := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₀ D₁ F U hIm ω hω c hc
  obtain ⟨w₁, hw₁, hw₁ω⟩ := hω
  obtain ⟨w₀, hw₀, hw₀ω⟩ := hc
  let W : Submodule K D₁.Zl := (D₀.Zl.map F.onPol).comap D₁.Zl.subtype
  have hW : W ≤ W.comap D₁.LcZ := by
    rintro z ⟨x, hx, hxz⟩
    refine ⟨D₀.Lc x, D₀.Lc_mem_Zl hx, ?_⟩
    rw [BKHom.onPol_Lc, hxz]
    rfl
  have hωZ : ω ∈ D₁.Zl := hw₁ω ▸ D₁.Lc_mem_Zl hw₁
  have hl : ((l : K) ^ c) ≠ 0 := pow_ne_zero _ (l_ne_zero (K := K) l)
  have hrange : (⟨ω, hωZ⟩ : D₁.Zl) ∈ LinearMap.range D₁.LcZ := ⟨⟨w₁, hw₁⟩, Subtype.ext hw₁ω⟩
  have hmemW : (⟨ω, hωZ⟩ : D₁.Zl) ∈ W := by
    refine ⟨((l : K) ^ c)⁻¹ • w₀, D₀.Zl.smul_mem _ hw₀, ?_⟩
    rw [map_smul, hw₀ω, smul_smul, inv_mul_cancel₀ hl, one_smul]
    rfl
  have hmap := hIm.2 W hW
  have h2 : (⟨ω, hωZ⟩ : D₁.Zl) ∈ W.map D₁.LcZ := hmap ▸ ⟨hrange, hmemW⟩
  obtain ⟨z, ⟨x, hx, hxz⟩, hzω⟩ := h2
  refine ⟨x, hx, ?_⟩
  rw [BKHom.onPol_Lc, hxz]
  exact congrArg Subtype.val hzω

end GlobalTheory.Proof.LiftImage
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_image_eulerE_invariants_quotient : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : BKHom D₀ D₁) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D₁ U → ∀ ω : D₁.Pol, (∃ w ∈ D₁.Zl, D₁.Lc w = ω) → ∀ c : ℕ, (∃ w₀ ∈ D₀.Zl, F.onPol w₀ = (l : K) ^ c • ω) → ∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = ω := by
  atlas_forward_decl GlobalTheory.Proof.LiftImage.lift_image
end

section
open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem smul_pow_mem_span_pow_smul_top {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (l : O) (j n : ℕ) (x : M) (h : n ≤ j) :
    l ^ j • x ∈ (Ideal.span {l}) ^ n • (⊤ : Submodule O M) := by
  rw [Ideal.span_singleton_pow]
  have e : l ^ j • x = l ^ n • (l ^ (j - n) • x) := by
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem map_mem_pow_smul_top {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (I : Ideal O) (n : ℕ) (f : M →ₗ[O] N) {x : M}
    (hx : x ∈ I ^ n • (⊤ : Submodule O M)) : f x ∈ I ^ n • (⊤ : Submodule O N) := by
  have hle : I ^ n • (⊤ : Submodule O M) ≤ (I ^ n • (⊤ : Submodule O N)).comap f := by
    rw [Submodule.smul_le]
    intro r hr y _
    simp only [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact hle hx

theorem successive_approximation : ∀ {O Y Z : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup Z] [Module O Z] (l : O) [IsAdicComplete (Ideal.span {l}) Y]
    [IsHausdorff (Ideal.span {l}) Z] (Lc P : Y →ₗ[O] Z) (W : Submodule O Z) (c k : ℕ), c < k →
    (∀ y, Lc y ∈ W ∧ (Lc + l ^ k • P) y ∈ W) → (∀ z, l • z ∈ W → z ∈ W) →
    (∀ z ∈ W, l ^ c • z ∈ LinearMap.range Lc) → ∀ y₀ : Y, ∃ y, (Lc + l ^ k • P) y = Lc y₀ := by
  intro O Y Z _ _ _ _ _ l _ _ Lc P W c k hck hW hsat hrange y₀
  have hsatn : ∀ n z, l ^ n • z ∈ W → z ∈ W := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih =>
      intro z h
      apply ih
      apply hsat
      rwa [smul_smul, ← pow_succ']
  have hPW : ∀ y, P y ∈ W := by
    intro y
    apply hsatn k
    have h := W.sub_mem (hW y).2 (hW y).1
    simpa [LinearMap.add_apply, LinearMap.smul_apply] using h
  have hg : ∀ v, ∃ u, Lc u = l ^ c • P v := fun v => by
    obtain ⟨u, hu⟩ := hrange _ (hPW v)
    exact ⟨u, hu⟩
  choose g hg using hg
  obtain ⟨d, hd, hk⟩ : ∃ d, 1 ≤ d ∧ k = d + c := ⟨k - c, by omega, by omega⟩
  let L' : Y →ₗ[O] Z := Lc + l ^ k • P
  have hL' : ∀ y, L' y = Lc y + l ^ k • P y := fun y => rfl
  let s : ℕ → Y × Y := fun n =>
    Nat.rec (y₀, -y₀) (fun i p => (p.1 + l ^ ((i + 1) * d) • g p.2, -g p.2)) n
  have s_succ : ∀ n, s (n + 1) = ((s n).1 + l ^ ((n + 1) * d) • g (s n).2, -g (s n).2) :=
    fun n => rfl
  have s_zero : s 0 = (y₀, -y₀) := rfl
  have inv : ∀ n, Lc y₀ - L' (s n).1 = l ^ (n * d) • l ^ k • P (s n).2 := by
    intro n
    induction n with
    | zero =>
      rw [s_zero, hL']
      simp
    | succ n ih =>
      rw [s_succ]
      simp only
      rw [map_add, map_smul, ← sub_sub, ih, hL', hg, map_neg, smul_neg, smul_add, smul_smul,
        smul_smul, smul_smul, ← pow_add, ← pow_add, ← pow_add]
      have e : n * d + k = (n + 1) * d + c := by
        rw [hk, add_mul, one_mul, add_assoc]
      rw [e, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg, smul_smul, ← pow_add]
  have hcauchy : ∀ a b, a ≤ b → (s a).1 ≡ (s b).1 [SMOD (Ideal.span {l}) ^ a • (⊤ : Submodule O Y)] := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih =>
      rw [SModEq.sub_mem] at ih ⊢
      rw [s_succ]
      simp only
      have h2 := smul_pow_mem_span_pow_smul_top l ((b + 1) * d) a (g (s b).2)
        (by nlinarith)
      have := Submodule.sub_mem _ ih h2
      rwa [sub_sub] at this
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete) (fun {a b} h => hcauchy a b h)
  refine ⟨y, ?_⟩
  have key : Lc y₀ - L' y = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {l})
    intro n
    rw [SModEq.sub_mem, sub_zero]
    have h1 : Lc y₀ - L' y = (Lc y₀ - L' (s n).1) + L' ((s n).1 - y) := by
      rw [map_sub]; abel
    rw [h1, inv, smul_smul, ← pow_add]
    refine Submodule.add_mem _ (smul_pow_mem_span_pow_smul_top l _ n _ (by nlinarith)) ?_
    exact map_mem_pow_smul_top _ n L' ((SModEq.sub_mem).mp (hy n))
  exact (sub_eq_zero.mp key).symm

end GlobalTheory
end

section
section
noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in
theorem natCast_l_ne_zero : (l : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K)]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem exists_Mon_eq_Lc_cls : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hU hUI hUc hη1 hηH hl hl2 hC hS y hy
  have hlK : (l : K) ≠ 0 := natCast_l_ne_zero
  set k : ℕ := l - 14 * H with hk
  have hlk : ((l : K) ^ k) ≠ 0 := pow_ne_zero _ hlK
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hηH hl2
  have hcomp := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH hl2
  have hY'Y : ∀ {y : Vec K a ι}, y ∈ D.Y' → y ∈ D.Y := fun h => D.desc.Y'_le_Y η h

  let LcK : Vec K a ι →ₗ[K] D.Pol := D.Lc ∘ₗ D.cls
  have hLc : ∀ v : D.Y', LcK.restrictScalars O (v : Vec K a ι) ∈ D.Z := fun v =>
    hint _ (D.desc.cls_mem_Z (hY'Y v.2))
  let Lc' : D.Y' →ₗ[O] D.Z := ((LcK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hLc

  let PK : Vec K a ι →ₗ[K] D.Pol := -((l : K) ^ k)⁻¹ • (D.cls ∘ₗ mulV K a ι (E K l e) ∘ₗ D.zeta)
  have hPK : ∀ y : Vec K a ι, PK y = -((l : K) ^ k)⁻¹ • D.cls (E K l e • D.zeta y) := fun y => by
    simp [PK]
  have hP : ∀ v : D.Y', PK.restrictScalars O (v : Vec K a ι) ∈ D.Z := by
    intro v
    have hv := v.2
    obtain ⟨p, hp, f, hf, hz⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη1 hηH (by omega) v hv
    have hEf : D.cls (E K l e • f) = 0 := by
      rw [PhiMod.cls_eq_zero_iff]
      have h1 := hcomp.2.1 f hf
      have h2 := D.smul_mem_Man (pow_mem (A_le_Rpi l e (E_mem l e (A O K))) (2 * H + 1)) h1
      rwa [smul_smul, ← Ezpow_natCast, ← Ezpow_add, show ((2 * H + 1 : ℕ) : ℤ) + -(2 * H : ℤ) = 1 by push_cast; ring,
        show (1 : ℤ) = ((1 : ℕ) : ℤ) by rfl, Ezpow_natCast, pow_one] at h2
    have hval : PK (v : Vec K a ι) = D.cls (-(E K l e • p)) := by
      rw [hPK, hz, smul_add, smul_comm (E K l e) ((l : K) ^ k) p,
        smul_comm (E K l e) (((l : K) ^ (3 * H))⁻¹) f, map_add, map_smul D.cls ((l : K) ^ k), map_smul D.cls ((l : K) ^ (3 * H))⁻¹, hEf, smul_zero, add_zero,
        smul_smul, neg_mul, inv_mul_cancel₀ hlk, neg_smul, one_smul, map_neg]
    refine D.desc.mem_Z.2 ⟨⟨-(E K l e • p), ?_, hval.symm⟩, fun g => ?_⟩
    · refine neg_mem ?_
      rw [mem_divE, smul_comm]
      exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)
    · have h : D.cls (E K l e • D.zeta v) = D.Lc (D.cls v) - D.Mon v := by
        rw [D.Mon_eq, sub_sub_cancel]
      have hinv : D.cls (E K l e • D.zeta v) ∈ D.desc.actPol.invariants := by
        rw [h]
        refine sub_mem (fun g => ?_) (D.desc.Mon_mem_invariants (hY'Y hv).2)
        rw [BKDat.actPol_Lc, D.desc.cls_mem_invariants (hY'Y hv).2 g]
      have h2 : PK v ∈ D.desc.actPol.invariants := by
        rw [hPK]
        exact Submodule.smul_mem _ _ hinv
      exact h2 g
  let P : D.Y' →ₗ[O] D.Z := ((PK.restrictScalars O).comp D.Y'.subtype).codRestrict D.Z hP
  have hLc'apply : ∀ v : D.Y', (Lc' v : D.Pol) = D.Lc (D.cls v) := fun v => rfl
  have hPapply : ∀ v : D.Y', (P v : D.Pol) = PK v := fun v => rfl
  have hsum : ∀ v : D.Y', (((Lc' + (l : O) ^ k • P) v : D.Z) : D.Pol) = D.Mon v := by
    intro v
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul_of_tower,
      hLc'apply, hPapply, hPK, ← algebraMap_smul K ((l : O) ^ k), map_pow, map_natCast, smul_smul, mul_neg,
      mul_inv_cancel₀ hlk, neg_one_smul, D.Mon_eq, sub_eq_add_neg]
  let W : Submodule O D.Z := ((D.Zl.map D.Lc).restrictScalars O).comap D.Z.subtype
  have hW : ∀ z : D.Z, z ∈ W ↔ ∃ w ∈ D.Zl, D.Lc w = z := fun z => Iff.rfl
  have hc : η + (N + 1) * η < k := by
    have : (N + 2) * η = η + (N + 1) * η := by ring
    omega
  have h1 : ∀ v, Lc' v ∈ W ∧ (Lc' + (l : O) ^ k • P) v ∈ W := by
    intro v
    refine ⟨(hW _).2 ⟨D.cls v, D.desc.mem_Zl_of_mem_Z (D.desc.cls_mem_Z (hY'Y v.2)), rfl⟩, (hW _).2 ?_⟩
    rw [hsum]
    obtain ⟨-, w, hw, h⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D v
      (D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hY'Y v.2⟩)
    exact ⟨w, hw, h⟩
  have h2 : ∀ z : D.Z, (l : O) • z ∈ W → z ∈ W := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW _).1 hz
    refine (hW _).2 ⟨((l : K))⁻¹ • w, D.Zl.smul_mem _ hw, ?_⟩
    rw [map_smul, h, Submodule.coe_smul_of_tower, ← algebraMap_smul K (l : O), map_natCast, smul_smul,
      inv_mul_cancel₀ hlK, one_smul]
  have h3 : ∀ z ∈ W, (l : O) ^ (η + (N + 1) * η) • z ∈ LinearMap.range Lc' := by
    intro z hz
    obtain ⟨w, hw, h⟩ := (hW z).1 hz
    obtain ⟨y', hy', hy'eq⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι η H D U N hU hUI hUc hηH (by omega) hl2 0 w hw
      (by rw [pow_zero, one_smul, h]; exact z.2)
    refine ⟨⟨y', hy'⟩, Subtype.ext ?_⟩
    rw [hLc'apply, Submodule.coe_smul_of_tower, ← algebraMap_smul K ((l : O) ^ (η + (N + 1) * η)), map_pow, map_natCast, ← h, hy'eq,
      zero_add]
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.successive_approximation (l : O) Lc' P W (η + (N + 1) * η) k hc h1 h2 h3 ⟨y, hy⟩
  refine ⟨y₁, y₁.2, ?_⟩
  have := congrArg Subtype.val hy₁
  rw [hsum] at this
  exact this

end GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  atlas_forward_decl GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls
end

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Lim

variable {K : Type} [NormedField K]

theorem exists_lim_of_norm_sub_le_pow [CompleteSpace K] {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {c : ℕ → K} (h : ∀ m n, m ≤ n → ‖c n - c m‖ ≤ r ^ m) : ∃ x, ∀ n, ‖c n - x‖ ≤ r ^ n := by
  have hc : CauchySeq c := by
    refine cauchySeq_of_le_tendsto_0 (fun N => r ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr)
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hnm
    · rw [norm_sub_rev]
      exact (h n m hnm).trans (pow_le_pow_of_le_one hr0 hr.le hn)
    · exact (h m n hnm).trans (pow_le_pow_of_le_one hr0 hr.le hm)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun n => ?_⟩
  have ht : Tendsto (fun m => ‖c n - c m‖) atTop (𝓝 ‖c n - x‖) :=
    (tendsto_const_nhds.sub hx).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [norm_sub_rev]
  exact h n m hm

theorem eq_zero_of_norm_le_pow_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {x : K}
    (h : ∀ n, ‖x‖ ≤ r ^ n) : x = 0 :=
  norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr) h)

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] in

theorem pow_l_smul_vec_eq (n : ℕ) (v : Vec K a ι) : ((l : O) ^ n) • v = ((l : K) ^ n) • v := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem norm_coeff_pow_l_smul_le {P : PhiMod O K l e a ι} {t : Vec K a ι} (ht : t ∈ P.M) (n : ℕ)
    (τ : ZMod a) (i : ι) (k : ℕ) : ‖coeff k ((((l : K) ^ n) • t) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
  simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (mem_A.1 (mem_vecs.1 (mem_tot.1 ht τ) i) k)

theorem pow_l_inv_smul_mem_M {P : PhiMod O K l e a ι} {v : Vec K a ι} {n : ℕ}
    (h : ∀ τ i k, ‖coeff k (v τ i)‖ ≤ ‖(l : K)‖ ^ n) : ((l : K) ^ n)⁻¹ • v ∈ P.M :=
  mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => by
    simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_inv, norm_pow]
    have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact h τ i k

variable [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

variable (D : BKDat O K l e a ι η H)

theorem mem_Y'_iff_coeff {v : Vec K a ι} : v ∈ D.Y' ↔ E K l e ^ η • v ∈ D.M ∧
    (∀ g, D.desc.act g v = v) ∧ ∀ τ i k, k < e → coeff k (v τ i) = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, rfl⟩ := (Descent.mem_Y' _).1 hv
    have h2 := (Descent.mem_invOf _).1 (Descent.Y'_le_Y _ η hv)
    refine ⟨mem_divE.1 h2.1, h2.2, fun τ i k hk => ?_⟩
    show coeff k ((X : K⟦X⟧) ^ e * y τ i) = 0
    rw [coeff_X_pow_mul', if_neg (by omega)]
  · rintro ⟨h1, h2, h3⟩
    have hd : ∀ τ i, (X : K⟦X⟧) ^ e ∣ v τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => h3 τ i k hk
    choose y hy using hd
    have hv : v = (X : K⟦X⟧) ^ e • (y : Vec K a ι) := funext fun τ => funext fun i => hy τ i
    have hXinj : ∀ w w' : Vec K a ι, (X : K⟦X⟧) ^ e • w = (X : K⟦X⟧) ^ e • w' → w = w' :=
      fun w w' h => funext fun τ => funext fun i =>
        mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (congrFun (congrFun h τ) i)
    refine (Descent.mem_Y' _).2 ⟨y, (Descent.mem_invOf _).2 ⟨mem_divE.2 ?_, fun g => hXinj _ _ ?_⟩, hv.symm⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => ?_
      have := mem_A.1 (mem_vecs.1 (mem_tot.1 h1 τ) i) (k + e)
      have h4 : (E K l e ^ η • v) τ i = (X : K⟦X⟧) ^ e * (E K l e ^ η • y) τ i := by
        rw [hv]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rwa [h4, coeff_X_pow_mul] at this
    · rw [← D.desc.act_X_pow_smul, ← hv, h2 g]

theorem smodEq_Y'_iff (x y : D.Y') (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(l : O)} ^ n • ⊤ : Submodule O D.Y')] ↔
      ∃ z ∈ D.Y', (x : Vec K a ι) - y = ((l : K) ^ n) • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩
    refine ⟨b, b.2, ?_⟩
    rw [← pow_l_smul_vec_eq (O := O)]
    exact (congrArg Subtype.val hb).symm
  · rintro ⟨z, hz, h⟩
    refine ⟨⟨z, hz⟩, Submodule.mem_top, Subtype.ext ?_⟩
    show ((l : O) ^ n) • z = (x : Vec K a ι) - y
    rw [pow_l_smul_vec_eq, h]

theorem isHausdorff_Y' : IsHausdorff (Ideal.span {(l : O)}) D.Y' := ⟨fun x hx => by
  have hE : ∀ n τ i k, ‖coeff k ((E K l e ^ η • (x : Vec K a ι)) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff x 0 n).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at h
    rw [h, smul_comm]
    exact norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 n
  have h0 : E K l e ^ η • (x : Vec K a ι) = 0 := funext fun τ => funext fun i => ext fun k =>
    eq_zero_of_norm_le_pow_of_lt_one (norm_nonneg _) (norm_l_lt_one l) fun n => hE n τ i k
  exact Subtype.ext (((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 (h0.trans (smul_zero _).symm))⟩

theorem isPrecomplete_Y' : IsPrecomplete (Ideal.span {(l : O)}) D.Y' := ⟨fun f hf => by
  have hl0 : ∀ n, ((l : K) ^ n) ≠ 0 := fun n => pow_ne_zero _ (l_ne_zero l)
  have hr0 : (0 : ℝ) ≤ ‖(l : K)‖ := norm_nonneg _
  have hr1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
  have hfY : ∀ n, _ := fun n => (D.mem_Y'_iff_coeff).1 (f n).2
  set s : ℕ → Vec K a ι := fun n => E K l e ^ η • (f n : Vec K a ι) with hs_def
  have hs : ∀ m n, m ≤ n → ∀ τ i k, ‖coeff k (s n τ i) - coeff k (s m τ i)‖ ≤ ‖(l : K)‖ ^ m := by
    intro m n hmn τ i k
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff _ _ m).1 (hf hmn)
    have h' : s m - s n = ((l : K) ^ m) • (E K l e ^ η • z) := by
      simp only [hs_def]
      rw [← smul_sub, h, smul_comm]
    have := norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 m τ i k
    rw [← h', Pi.sub_apply, Pi.sub_apply, map_sub] at this
    rwa [norm_sub_rev]
  choose w hw using fun p : ZMod a × ι × ℕ =>
    exists_lim_of_norm_sub_le_pow hr0 hr1 (c := fun n => coeff p.2.2 (s n p.1 p.2.1))
      (fun m n hmn => hs m n hmn p.1 p.2.1 p.2.2)
  set W : Vec K a ι := fun τ i => PowerSeries.mk fun k => w (τ, i, k) with hW_def
  have hW : ∀ n τ i k, ‖coeff k ((s n - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun n τ i k => by
    simpa [hW_def] using hw (τ, i, k) n

  have hsinv : ∀ n g, D.desc.act g (s n) = s n := fun n g => by
    simp only [hs_def]
    rw [D.desc.act_E_pow_smul, (hfY n).2.1 g]
  have hWinv : ∀ g, D.desc.act g W = W := fun g => by
    have hsm : ∀ n τ i k, ‖coeff k ((D.desc.act g W - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
      intro n
      have hb : ∀ τ i k, ‖coeff k ((W - s n) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun τ i k => by
        rw [Pi.sub_apply, Pi.sub_apply, map_sub, norm_sub_rev, ← map_sub, ← Pi.sub_apply,
          ← Pi.sub_apply]
        exact hW n τ i k
      have ht := pow_l_inv_smul_mem_M (P := D.toPhiMod) hb
      set t := ((l : K) ^ n)⁻¹ • (W - s n) with ht_def
      have hWt : W - s n = ((l : K) ^ n) • t := by rw [ht_def, smul_inv_smul₀ (hl0 n)]
      have : D.desc.act g W - W = ((l : K) ^ n) • (D.desc.act g t - t) := by
        rw [smul_sub, ← map_smul, ← hWt, map_sub, hsinv n g]
        abel
      rw [this]
      exact norm_coeff_pow_l_smul_le (sub_mem (D.desc.act_mem_M g t ht) ht) n
    exact sub_eq_zero.1 (funext fun τ => funext fun i => ext fun k =>
      eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => hsm n τ i k)
  have hWlow : ∀ τ i, (X : K⟦X⟧) ^ e ∣ W τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => by
    have h0 : coeff k (s 0 τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s 0 τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY 0).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    refine eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => ?_
    have h1 : coeff k (s n τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s n τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    have := hW n τ i k
    rwa [Pi.sub_apply, Pi.sub_apply, map_sub, h1, zero_sub, norm_neg] at this

  obtain ⟨u, hu⟩ := (isUnit_E (K := K) l e).pow η
  set L : Vec K a ι := ((u⁻¹ : K⟦X⟧ˣ) : K⟦X⟧) • W with hL_def
  have hEL : E K l e ^ η • L = W := by
    rw [hL_def, smul_smul, ← hu, Units.mul_inv, one_smul]
  have hLinv : ∀ g, D.desc.act g L = L := fun g => by
    refine ((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 ?_
    rw [← D.desc.act_E_pow_smul, hEL, hWinv g]
  have key : ∀ n, ((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L) ∈ D.Y' := fun n => by
    refine (D.mem_Y'_iff_coeff).2 ⟨?_, fun g => ?_, fun τ i k hk => ?_⟩
    · rw [smul_comm, smul_sub, hEL]
      exact pow_l_inv_smul_mem_M (hW n)
    · rw [map_smul, map_sub, (hfY n).2.1 g, hLinv g]
    · have hdv : (X : K⟦X⟧) ^ e ∣ (((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L)) τ i := by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_C_mul]
        refine Dvd.dvd.mul_left (dvd_sub (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) ?_) _
        simp only [hL_def, Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_left (hWlow τ i) _
      exact X_pow_dvd_iff.1 hdv k hk
  have hLmem : L ∈ D.Y' := by
    have := sub_mem (f 0).2 (key 0)
    rwa [pow_zero, inv_one, one_smul, sub_sub_cancel] at this
  refine ⟨⟨L, hLmem⟩, fun n => (D.smodEq_Y'_iff _ _ n).2 ⟨_, key n, ?_⟩⟩
  exact (smul_inv_smul₀ (hl0 n) _).symm⟩

end BKDat

theorem BKDat.isAdicComplete_Y' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H),
    IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact { toIsHausdorff := D.isHausdorff_Y', toIsPrecomplete := D.isPrecomplete_Y' }

end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_twistedInvariantLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  atlas_forward_decl GlobalTheory.BK.BKDat.isAdicComplete_Y'
end

section
section
namespace GlobalTheory.InertiaEigenvalues.FreeHausdorff

open PowerSeries GlobalTheory.BK

theorem eq_zero_of_mem_pow {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) {y : O}
    (hy : ∀ n : ℕ, y ∈ Ideal.span {(l : O)} ^ n) : y = 0 := by
  have hb : ∀ n : ℕ, ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    have h := hy n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨a, rfl⟩ := h
    have ha : ‖algebraMap O K a‖ ≤ 1 :=
      (IsUnitBall.mem_range_iff (O := O) (algebraMap O K a)).1 ⟨a, rfl⟩
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    calc ‖algebraMap O K a‖ * ‖(l : K)‖ ^ n ≤ 1 * ‖(l : K)‖ ^ n :=
          mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) n)
      _ = ‖(l : K)‖ ^ n := one_mul _
  have h0 : ‖algebraMap O K y‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl) hb
  have h1 : algebraMap O K y = 0 := norm_le_zero_iff.1 h0
  exact IsUnitBall.inj (K := K) (h1.trans (map_zero _).symm)

theorem isHausdorff_ring {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] {l : ℕ} (hl : ‖(l : K)‖ < 1) : IsHausdorff (Ideal.span {(l : O)}) O := by
  refine ⟨fun x hx => eq_zero_of_mem_pow (K := K) hl fun n => ?_⟩
  have h := SModEq.sub_mem.1 (hx n)
  simpa [smul_eq_mul, Ideal.mul_top] using h

theorem isHausdorff_of_free {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (I : Ideal R) [h : IsHausdorff I R] : IsHausdorff I M := by
  refine ⟨fun x hx => ?_⟩
  let b := Module.Free.chooseBasis R M
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine h.haus _ fun n => ?_
  have hxn : x ∈ I ^ n • (⊤ : Submodule R M) := by simpa using SModEq.sub_mem.1 (hx n)
  have hle : (I ^ n • (⊤ : Submodule R M)).map (b.coord i) ≤ I ^ n • (⊤ : Submodule R R) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have := hle (Submodule.mem_map_of_mem hxn)
  rw [SModEq.sub_mem, sub_zero]
  simpa using this

end GlobalTheory.InertiaEigenvalues.FreeHausdorff

namespace GlobalTheory.InertiaEigenvalues

open PowerSeries GlobalTheory.BK

theorem isHausdorff_Z_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hD
  haveI : Module.Free O D.Z := hD.1
  haveI : IsHausdorff (Ideal.span {(l : O)}) O :=
    FreeHausdorff.isHausdorff_ring (K := K) (norm_l_lt_one (K := K) l)
  exact FreeHausdorff.isHausdorff_of_free _

end GlobalTheory.InertiaEigenvalues
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  atlas_forward_decl GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.InertiaEigenvalues

theorem lifting_along_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  intro O K _ _ _ _ _ l e a _ _ _ _ _ _ ι₀ ι₁ ι₂ _ _ _ _ _ _ η H D₀ D₁ D₂ F G N Sig U hH y₂ hy₂ m₂ hm₂ h0
  obtain ⟨hex, hnum, htype, hch2⟩ := hH
  have hl : l.Prime := Fact.out
  have hts : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  obtain ⟨hr1, hr4, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha hts Sig N hnum.frob_mem hnum.zero_mem_Sig
    hnum.card_Sig hnum.two_le
  set r := maxPeriod l Sig with hr
  obtain ⟨hL1, hL2, hL3, -, -, hL6⟩ :=
    GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η r hnum.two_le hnum.one_le hnum.lt hr4 hnum.large
  have hl2 : l ≠ 2 := by
    have h8 : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hnum.two_le 3
    have := hnum.large
    generalize H * N ^ 2 = A at this
    generalize N ^ 3 = B at this h8
    omega

  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hnum.frob_mem, hnum.zero_mem_Sig, hnum.card_Sig, hnum.two_le, hnum.range_U, hnum.zero_mem_U,
      hnum.card_U, hnum.one_le, hnum.lt, hnum.large⟩
  obtain ⟨-, hkM, -, hkMinv, -, hkY'⟩ :=
    GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow O K l e a ι₁ ι₂ Sig U N η H hB D₁ D₂ htype hch2 G hex.finiteLength
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N r with hρ
  have hcast : ∀ v : Vec K a ι₂, (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N : ℕ) • v = (l : K) ^ ρ • v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul K]
    push_cast
    rfl
  obtain ⟨y₁, hy₁, hGy₁⟩ := hkY' y₂ hy₂
  obtain ⟨m₁, hm₁, hGm₁⟩ := hkMinv m₂ hm₂
  rw [hcast] at hGy₁ hGm₁
  have hG1 : G.app (y₁ + D₁.phi m₁) = (l : K) ^ ρ • (y₂ + D₂.phi m₂) := by
    rw [map_add, G.app_phi, hGy₁, hGm₁, map_smul, smul_add]

  set ω := D₁.Mon (y₁ + D₁.phi m₁) with hω
  have hω1 : (l : K) ^ (η * (r + 1)) • ω ∈ D₁.Z :=
    GlobalTheory.T.breuilKisinDescent_pow_smul_monodromy_add_phi_mem O K l e a ι₁ η H D₁ hnum.one_le hnum.lt (by omega) hL2 r hr1
      (fun τ c hc => hrper c (htype.chars_subset τ hc)) hL6 hl2 y₁ hy₁ m₁ hm₁

  obtain ⟨hjmp, -, hinj, hker⟩ := GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι₀ ι₁ ι₂ η H D₀ D₁ D₂ F G hex
  have hGω : G.onPol ((l : K) ^ (η * (r + 1)) • ω) = 0 := by
    rw [map_smul, hω, G.onPol_Mon, hG1, map_smul, h0, smul_zero, smul_zero]
  obtain ⟨w₀, hw₀, hFw₀⟩ := hker ρ (fun y hy => by
      obtain ⟨x, hx, h⟩ := hkM y hy
      exact ⟨x, hx, h.trans (hcast y)⟩) _ hω1 hGω
  rw [smul_smul, ← pow_add] at hFw₀
  have hy₁Y : y₁ + D₁.phi m₁ ∈ D₁.Yl := by
    refine D₁.desc.mem_Yl_iff.2 ⟨0, ?_⟩
    rw [pow_zero, one_smul]
    refine add_mem (D₁.desc.Y'_le_Y η hy₁) ⟨?_, fun g => ?_⟩
    · exact (mem_divE (l := l) (e := e)).2 (D₁.upper _ (D₁.phi_mem_L hm₁.1))
    · rw [D₁.desc.act_phi, hm₁.2 g]
  obtain ⟨-, wm, hwm, hLcwm⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι₁ η H D₁ _ hy₁Y
  have hIm := (GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι₁ η H D₁ U N htype.jumps_subset
    (fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)) hnum.card_U hnum.lt).1
  obtain ⟨w', hw', hFw'⟩ := GlobalTheory.T.lift_image_eulerE_invariants_quotient O K l e a ι₀ ι₁ η H D₀ D₁ F U hIm ω
    ⟨wm, hwm, hLcwm⟩ _ ⟨w₀, D₀.desc.mem_Zl_of_mem_Z hw₀, hFw₀⟩

  set c₂ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂ N η r with hc₂
  have hw₀eq : (l : K) ^ c₂ • D₀.Lc w' = w₀ := by
    apply hinj
    rw [map_smul, hFw', hFw₀, hc₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁, add_comm]
  have hjmp0 : D₀.jumps ⊆ (U : Set ℤ) := hjmp.trans htype.jumps_subset
  have hIcc : U ⊆ Finset.Icc (-(η : ℤ)) H := fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)
  obtain ⟨y, hy, hLcy⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.lt (by omega) hL2 c₂ w' hw' (hw₀eq ▸ hw₀)

  have hff := (GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime O K l e a ι₀ η H D₀).1
  obtain ⟨y₀, hy₀, hMy₀⟩ := GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.one_le hnum.lt hL3 hL2 (GlobalTheory.T.isAdicComplete_twistedInvariantLattice O K l e a ι₀ η H D₀)
    (GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree O K l e a ι₀ η H D₀ hff) y hy

  have hGF : ∀ v : Vec K a ι₀, G.app (F.app v) = 0 := by
    intro v
    rw [eq_sum_bas v, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [F.app_smul_tot, G.app_smul_tot]
    have h1 : F.app (bas i) ∈ D₁.M := F.app_mem_M (D₀.bas_mem_M i)
    rw [(hex.exact _ h1).2 ⟨bas i, D₀.bas_mem_M i, rfl⟩, smul_zero]
  set n := c₂ + η + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL N η with hn
  have hs {κ : Type} (v : Vec K a κ) : ((l : O) ^ n) • v = (l : K) ^ n • v := by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  have h3 : ((l : O) ^ n • y₁ - F.app y₀) + D₁.phi ((l : O) ^ n • m₁) =
      (l : K) ^ n • (y₁ + D₁.phi m₁) - F.app y₀ := by
    rw [hs, hs, map_smul, smul_add]
    abel
  refine ⟨_, sub_mem (Submodule.smul_mem _ ((l : O) ^ n) hy₁) (F.app_mem_Y' hy₀), _,
    Submodule.smul_mem _ ((l : O) ^ n) hm₁, ?_, ?_⟩
  · rw [h3, map_sub, map_smul, ← hω, ← F.onPol_Mon, hMy₀, hLcy, map_smul, hFw']
    exact sub_self _
  · rw [h3, map_sub, G.app.map_smul_of_tower, hGF, sub_zero, hG1, smul_smul, ← pow_add]
    rfl

end GlobalTheory.InertiaEigenvalues
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingTheorem_phiModules_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  atlas_forward_decl GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple
end

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem padicValNat_factorial_le_sub (l i j : ℕ) [hp : Fact l.Prime] (hji : j ≤ i) (hjl : j < l) :
    padicValNat l i.factorial ≤ i - j := by
  have hL := sub_one_mul_padicValNat_factorial (p := l) i
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  have hpos : 0 < (l.digits i).sum := by
    rcases Nat.eq_zero_or_pos (l.digits i).sum with h0 | h0
    · exfalso
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hi.ne'
      have h1 := Nat.getLast_digit_ne_zero l hi.ne'
      have h2 := List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne)
      exact h1 h2
    · exact h0
  have hsum : (l.digits i).sum ≤ i := Nat.digit_sum_le l i
  have hl2 := hp.out.two_le
  set v := padicValNat l i.factorial
  rcases Nat.eq_zero_or_pos v with hv | hv
  · omega
  · have : (l - 1) * v ≤ i - 1 := by omega
    clear_value v
    have h3 : v + (l - 1) ≤ (l - 1) * v + 1 := by
      obtain ⟨L, hLe⟩ : ∃ L, l - 1 = L + 1 := ⟨l - 2, by omega⟩
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [hLe]
      nlinarith
    omega

section Padic

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] in

theorem norm_pow_sub_le_norm_factorial {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ‖(l : K)‖ ^ (i - j) ≤ ‖(i.factorial : K)‖ := by
  rw [norm_l, norm_natCast_eq l, Padic.norm_eq_zpow_neg_valuation (by
    exact_mod_cast i.factorial_ne_zero), Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ h1 (padicValNat_factorial_le_sub l i j hji hjl))

theorem C_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ S O K e := by
  rw [← monomial_zero_eq_C_apply]
  exact monomial_mem_S (mul_le_one₀ hc (wS_nonneg _ _) (wS_le_one _ _))

theorem exists_frob_E_eq (e : ℕ) [NeZero e] : ∃ d ∈ S O K e, frob K l (E K l e) = C (l : K) * d := by
  refine ⟨1 + monomial (e * l) ((l : K)⁻¹), add_mem (one_mem _) (monomial_mem_S ?_), ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv]
    have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    rw [inv_mul_le_one₀ h0]
    exact norm_natCast_le_of_dvd (Nat.dvd_factorial (Fact.out : l.Prime).pos le_rfl)
  · rw [E, map_add, map_pow, frob_X, map_natCast, monomial_eq_C_mul_X_pow, mul_add, mul_one,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ (l_ne_zero l), map_one, one_mul, ← pow_mul,
      mul_comm l e, add_comm, map_natCast]

theorem exists_frob_Ediv_eq (e : ℕ) [NeZero e] {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ∃ s ∈ S O K e, frob K l (Ediv K l e i) = C ((l : K) ^ j) * s := by
  obtain ⟨d, hd, hE⟩ := exists_frob_E_eq (O := O) (K := K) l e
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  refine ⟨C ((l : K) ^ (i - j) / (i.factorial : K)) * d ^ i, mul_mem (C_mem_S ?_) (pow_mem hd i), ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ (norm_pow_sub_le_norm_factorial l hji hjl) (norm_nonneg _)
  · have key : (i.factorial : K)⁻¹ * (l : K) ^ i = (l : K) ^ j * ((l : K) ^ (i - j) / (i.factorial : K)) := by
      rw [mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hji, div_eq_inv_mul]
    rw [Ediv, map_mul, frob_C, map_pow, hE, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, key,
      map_mul, mul_assoc]

theorem exists_frob_eq_of_mem_Fil (e : ℕ) [NeZero e] {j : ℕ} (hjl : j < l) {r : S O K e}
    (hr : r ∈ Fil O K l e j) : ∃ s ∈ S O K e, frob K l (r : K⟦X⟧) = C ((l : K) ^ j) * s := by
  obtain ⟨g, hg, h, rfl⟩ := (mem_Fil l).1 hr j
  have key : ∀ x ∈ FilPre O K l e j, ∃ s ∈ S O K e, frob K l (x : K⟦X⟧) = C ((l : K) ^ j) * s := by
    intro x hx
    have hx' : x ∈ Submodule.span (S O K e) {x : S O K e | ∃ i, j ≤ i ∧ (x : K⟦X⟧) = Ediv K l e i} := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      rw [hxi]
      exact exists_frob_Ediv_eq l e hi hjl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨t, ht, h2⟩ := hy
      exact ⟨s + t, add_mem hs ht, by rw [Subalgebra.coe_add, map_add, h1, h2, mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, h1⟩ := hx
      exact ⟨frob K l c * s, mul_mem (frob_mem_S l c.2) hs, by
        rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, h1]; ring⟩
  obtain ⟨s, hs, h1⟩ := key g hg
  refine ⟨s + frob K l h, add_mem hs (frob_mem_S l h.2), ?_⟩
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, map_add, map_mul, h1, mul_add]
  congr 2
  simp

end Padic

theorem phi_FilMM_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j hjl v hv
  refine Submodule.smul_induction_on (p := fun v => ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v')
    hv (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hfs⟩ := exists_frob_eq_of_mem_Fil l e hjl hr
    have h3 := D.l_pow_smul_phi_mem_MM (k := η) (D.smul_mem_Mext (A_le_S l e) hn)
    refine ⟨s • ((l : K) ^ η • D.phi n), PhiMod.smul_mem_MM _ hs h3, ?_⟩
    rw [Subalgebra.smul_def, PhiMod.phi_smul, hfs, ← smul_eq_C_mul, smul_assoc,
      smul_comm ((l : K) ^ η) ((l : K) ^ j), smul_comm ((l : K) ^ η) s]
  · obtain ⟨v₁, h₁, e₁⟩ := hx
    obtain ⟨v₂, h₂, e₂⟩ := hy
    exact ⟨v₁ + v₂, add_mem h₁ h₂, by rw [map_add, smul_add, e₁, e₂, smul_add]⟩

end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  atlas_forward_decl GlobalTheory.BK.phi_FilMM_mem
end

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

section Helpers

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {a : ℕ} {ι : Type}

theorem Epow_smul_mem_of_hasU (l e : ℕ) {B : Subalgebra O K⟦X⟧} [HasU B]
    (W : Submodule B (Vec K a ι)) (k : ℕ) {x : Vec K a ι} (hx : x ∈ W) : E K l e ^ k • x ∈ W := by
  have := W.smul_mem (EIn l e B ^ k) hx
  rwa [Subalgebra.smul_def, SubmonoidClass.coe_pow, coe_EIn] at this

theorem natPow_smul_mem {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] [Module K M]
    (W : Submodule R M) (l n : ℕ) {x : M} (hx : x ∈ W) : (l : K) ^ n • x ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact W.nsmul_mem hx _

end Helpers

theorem lpow_Epow_twistedMon_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D c h1 h2 h3 h4 y' hy' m hm hc
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hr : ((l : K) ^ (3 * H)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have IC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D h2 h4
  obtain ⟨p₁, hp₁, f₁, hf₁, h₁⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D h1 h2 h3 y' hy'
  obtain ⟨p', hp', f', hf', h'⟩ := IC.1 _ hc
  have hy : y' + D.phi m ∈ D.EM η := by
    refine add_mem ((D.desc.Y'_le_Y η hy').1 : y' ∈ D.EM η) ?_
    rw [mem_divE]
    exact D.upper _ (D.phi_mem_L hm.1)
  obtain ⟨p'', hp'', f'', hf'', h''⟩ := IC.2.2 _ hy
  set r : K := (l : K)
  set u : K⟦X⟧ := E K l e
  have hF : (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) ∈ D.FilMM (10 * H) :=
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ hf₁))
      (natPow_smul_mem _ _ _ (Epow_smul_mem_of_hasU l e _ _ hf')))
      (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hf''))
  refine ⟨u ^ (2 * H + 1) • (r ^ c • r ^ (l - 14 * H) • p₁) + u ^ (2 * H + 1) • p' - r ^ c • p'',
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hp₁)))
      (Epow_smul_mem_of_hasU l e _ _ hp')) (natPow_smul_mem _ _ _ hp''), _, hF, IC.2.1 _ hF, ?_⟩
  have hinv : (r ^ (3 * H))⁻¹ • (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) =
      u ^ (2 * H + 1) • (r ^ c • ((r ^ (3 * H))⁻¹ • f₁)) + u ^ (2 * H + 1) • f' - r ^ c • f'' := by
    rw [smul_sub, smul_add, inv_smul_smul₀ hr, inv_smul_smul₀ hr, smul_comm (r ^ (3 * H))⁻¹ (u ^ (2 * H + 1)),
      smul_comm (r ^ (3 * H))⁻¹ (r ^ c)]
  rw [hinv, map_add D.zeta, h₁, smul_sub, smul_smul (u ^ (2 * H)) u, ← pow_succ, smul_sub,
    smul_comm (r ^ c) (u ^ (2 * H + 1)), smul_add (r ^ c) _ (D.zeta (D.phi m)), h', h'']
  simp only [smul_add]
  abel

end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  atlas_forward_decl GlobalTheory.BK.lpow_Epow_twistedMon_decomp
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.ZetaDenominator

theorem zetaBound : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ N η H Sig U hA D hT y' hy' m hm hMon
  haveI : CompleteSpace K := by
    haveI := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
    exact FiniteDimensional.complete ℚ_[l] K
  have hl : l.Prime := Fact.out
  have ha : 1 ≤ a := NeZero.one_le
  obtain ⟨hr1, hrN, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha (TameDescentExponentData.succ_eq (K := K)) Sig N
    hA.frob_mem hA.zero_mem_Sig hA.card_Sig hA.two_le
  obtain ⟨-, n2, n3, -, -, n6⟩ := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hA.two_le hA.one_le hA.lt hrN hA.large
  have hl2 : l ≠ 2 := by have := hA.lt; have := hA.one_le; omega
  have hφm := GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D (maxPeriod l Sig) hr1
    (fun τ c hc => hrper c (hT.chars_subset τ hc)) n6 hl2 m hm
  obtain ⟨P0, hP0, F0, hF0, hQF, hdec⟩ := GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp O K l e a ι η H D (η * (maxPeriod l Sig + 1)) hA.one_le hA.lt
    (by have := hA.one_le; omega) (by omega) y' hy' m hm hφm
  show (l : K) ^ (η * (maxPeriod l Sig + 1)) • D.zeta (y' + D.phi m) ∈ D.MM
  set c₁ := η * (maxPeriod l Sig + 1)
  set y := y' + D.phi m
  set w := E K l e • D.zeta y - D.EN y with hw_def
  have hw : w ∈ D.Man := by
    have h : D.EN y - E K l e • D.zeta y ∈ D.Man := (D.cls_eq_zero_iff).1 (by rw [← PhiMod.Mon_apply]; exact hMon)
    have := D.Man.neg_mem h
    rwa [neg_sub] at this
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have hζ : D.zeta y = c • D.phi w := by
    have h1 : w = E K l e • (D.zeta y - D.conn y) := by simp only [hw_def, PhiMod.EN_apply, smul_sub]
    rw [h1, PhiMod.phi_smul, smul_smul, hcE]
    conv_lhs => rw [PhiMod.zeta_eq, PhiMod.lphi_apply]
    simp only [Nat.cast_smul_eq_nsmul]
  have hE1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    have := E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
    push_cast at this
    exact this
  set Q := Ezpow K l e (-(2 * H : ℤ)) • (((l : K) ^ (3 * H))⁻¹ • F0) with hQ_def
  set X0 := Ezpow K l e (-(2 * H : ℤ)) • P0 with hX0_def
  have hsplit : (l : K) ^ c₁ • w = X0 + Q := by
    have h : (l : K) ^ c₁ • w = Ezpow K l e (-(2 * H : ℤ)) • (E K l e ^ (2 * H) • ((l : K) ^ c₁ • w)) := by
      rw [smul_smul, mul_comm, hE1, one_smul]
    rw [h, smul_comm (E K l e ^ (2 * H)) ((l : K) ^ c₁) w, hdec, smul_add]
  have hQ : Q ∈ D.Man := by
    rw [hQ_def, smul_comm]
    exact D.Man.smul_mem _ hQF
  have hX0 : X0 ∈ D.Man := by
    have : X0 = (l : K) ^ c₁ • w - Q := by rw [hsplit, add_sub_cancel_right]
    rw [this]
    exact D.Man.sub_mem (D.Man.smul_mem _ hw) hQ
  have hX0E : X0 ∈ D.EM (2 * H + η) := by
    rw [mem_divE, hX0_def, smul_smul, pow_add, mul_right_comm, hE1, one_mul]
    exact D.upper _ hP0
  have hX0M : X0 ∈ D.M := PhiMod.mem_M_of_mem_Man _ hX0E hX0
  have hφX0 : D.phi X0 ∈ D.MM := PhiMod.ext_mono _ (A_le_S l e) (D.phi_mem_L hX0M)
  obtain ⟨v', hv', hv'eq⟩ := GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration O K l e a ι η H D (10 * H) (by omega) F0 hF0
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hF : D.phi F0 = (l : K) ^ (3 * H) • ((l : K) ^ (2 * H) • ((l : K) ^ (5 * H - η) • v')) := by
    apply smul_right_injective _ (pow_ne_zero η hl0)
    rw [show 10 * H = η + (3 * H + (2 * H + (5 * H - η))) by have := hA.lt; omega] at hv'eq
    simpa only [pow_add, mul_smul] using hv'eq
  have hfr : (l : K⟦X⟧) ^ (2 * H) * frob K l (Ezpow K l e (-(2 * H : ℤ))) = c ^ (2 * H) := by
    rw [← hcE, mul_pow, ← map_pow, mul_assoc, ← map_mul, hE1, map_one, mul_one]
  have hcast : ∀ (n : ℕ) (x : Vec K a ι), (l : K) ^ n • x = (l : K⟦X⟧) ^ n • x := by
    intro n x
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hφQ' : D.phi Q = c ^ (2 * H) • ((l : K) ^ (5 * H - η) • v') := by
    rw [hQ_def, PhiMod.phi_smul, map_smul, hF, inv_smul_smul₀ (pow_ne_zero _ hl0), hcast (2 * H), smul_smul, mul_comm (frob K l _), hfr]
  have hφQ : D.phi Q ∈ D.MM := by
    rw [hφQ']
    refine D.MM.smul_mem ⟨c ^ (2 * H), pow_mem hc _⟩ ?_
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv' _
  have key : (l : K) ^ c₁ • D.zeta y = c • (D.phi X0 + D.phi Q) := by
    rw [← map_add, ← hsplit, map_smul, hζ, smul_comm]
  rw [key]
  exact D.MM.smul_mem ⟨c, hc⟩ (add_mem hφX0 hφQ)

end GlobalTheory.ZetaDenominator
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  atlas_forward_decl GlobalTheory.ZetaDenominator.zetaBound
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_breuil_kisin_datum_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O) (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂), IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  first | exact @GlobalTheory.CocycleNat.main | exact GlobalTheory.CocycleNat.main | (intros; apply GlobalTheory.CocycleNat.main <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add, hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  atlas_forward_decl GlobalTheory.KerGood.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TheoremT

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem liftF_of_isGood : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  intro hBS hFon l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hNum T₁ T₂ g hg hG₁ hG₂
  have hN2 := hNum.two_le
  have hlarge := hNum.large
  have hHN : 4 * H ≤ H * N ^ 2 := by
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H h4
  have hl2 : l ≠ 2 := by intro h; subst h; nlinarith
  have h8 : 8 * H + 1 < l := by nlinarith
  obtain ⟨T₀, f, hSES, hG₀⟩ := GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice hFon l a e ϖ LL Pl AI hStd Sig U T₁ T₂ g hg hG₁
  obtain ⟨P₀, -⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₀ hG₀
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₁ hG₁
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₂ hG₂
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₀ T₁ P₀ P₁ f
  obtain ⟨G, hG⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₁ T₂ P₁ P₂ g
  have hEx := GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL (Fin P₀.n) (Fin P₁.n) (Fin P₂.n) P₀.D.toPhiMod P₁.D.toPhiMod
    P₂.D.toPhiMod T₀ T₁ T₂ P₀.R.I P₁.R.I P₂.R.I f g F.toHom G.toHom hSES hF hG
  have hAdm : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.Admissible l e N η H Sig U :=
    ⟨hNum.frob_mem, hNum.zero_mem_Sig, hNum.card_Sig, hNum.two_le, hNum.range_U, hNum.zero_mem_U,
      hNum.card_U, hNum.one_le, hNum.lt, hNum.large⟩
  have hpot₂ := GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ (Fin P₂.n) η H P₂.D T₂ P₂.R
  unfold LatHom.LiftF
  intro c hc

  obtain ⟨y₂, hy₂, hMon₂, hCl₂⟩ :=
    GlobalTheory.T.crystalline_class_from_monodromy_kernel_element hBS hFon l a e ϖ LL Pl AI hStd N η H Sig U hNum T₂ hG₂ P₂ c hc

  obtain ⟨y₂', hy₂', m₂, hm₂, hsum⟩ :=
    Submodule.mem_sup.1 ((GlobalTheory.T.prime_pow_divisibility_of_descentDatum _ _ l e a _ η H P₂.D).2 y₂ hy₂)
  have hrew : y₂' + P₂.D.phi m₂ = (l : ↥LL.1) ^ η • y₂ + (P₂.D.phi m₂ - m₂) := by
    rw [← hsum]; abel
  have hMon₂' : P₂.D.Mon (y₂' + P₂.D.phi m₂) = 0 := by
    rw [hrew, P₂.D.Mon_add_phi_sub _ (PhiMod.M_le_Man _ hm₂.1), LinearMap.map_smul, hMon₂, smul_zero]
  have hCl₂' : P₂.R.ClassOf (y₂' + P₂.D.phi m₂)
      ((l : ↥LL.1) ^ η • (l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
    rw [hrew]
    exact hpot₂.2.2.2 _ _ m₂ hm₂ (hpot₂.2.2.1 _ _ η hCl₂)

  obtain ⟨y', hy', m, hm, hMon, hGy⟩ :=
    GlobalTheory.T.liftingTheorem_phiModules_exact_triple _ _ l e a _ _ _ η H P₀.D P₁.D P₂.D F G N Sig U
      ⟨hEx, hNum, hP₁, hP₂.chars_subset⟩ y₂' hy₂' m₂ hm₂ hMon₂'

  have hζ := GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice _ _ l e a _ N η H Sig U hAdm P₁.D hP₁ y' hy' m hm hMon
  obtain ⟨κ₁, hκ₁, hCl₁⟩ := GlobalTheory.T.galoisClass_of_monodromy_eq_zero hFon l a e ϖ LL (Fin P₁.n) η H P₁.D T₁ P₁.R Pl AI hStd hNum.lt h8
    _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.add_phi_mem_Y hy' hm) hMon _ hζ

  have hnat := GlobalTheory.T.tame_breuil_kisin_datum_exists l a e _ _ (thetaW a LL) ϖ (Fin P₁.n) (Fin P₂.n) η H P₁.D P₂.D T₁ T₂ P₁.R P₂.R g G hG
    _ _ hCl₁
  have happ : G.app ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig • (y' + P₁.D.phi m)) =
      (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) •
        (y₂' + P₂.D.phi m₂) := by
    have happ0 : ∀ (k : ↥LL.1) (v : Vec (↥LL.1) a (Fin P₁.n)), G.app (k • v) = k • G.app v := by
      intro k v
      ext1 τ
      simp only [Hom.app_apply, Pi.smul_apply, Matrix.mulVec_smul]
    rw [happ0, hGy, smul_smul, ← pow_add]
  rw [happ] at hnat
  have hCl := hpot₂.2.2.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) hCl₂'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hCl
  have hB := hpot₂.2.1 _ _ _ hnat hCl

  have hexp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) ≤ 7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁,
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    generalize maxPeriod l Sig = r
    have h1 : n + 2 - 1 = n + 1 := by omega
    rw [h1]
    nlinarith [Nat.zero_le (n * r), Nat.zero_le (η * n), Nat.zero_le (η * r)]
  rw [← algebraMap_smul (↥LL.1), map_pow, map_natCast, Pl.PD_p,
    ← Nat.sub_add_cancel hexp, pow_add, mul_smul]
  obtain ⟨β, hβ, hβeq⟩ : ∃ β ∈ latticeCoboundaries T₂.L, (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig)) • c = LatHom.post g κ₁ - β := ⟨_, hB, by abel⟩
  rw [hβeq, smul_sub]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hκ₁)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hβ

end GlobalTheory.TheoremT
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_surjection_good_crystalline_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  atlas_forward_decl GlobalTheory.TheoremT.liftF_of_isGood
end
