import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupport
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionRecursion
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartLatticePowerSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinear

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.EffN

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ∏ j, (ℓ j).h z ^ n j)
    {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  exact contDiffOn_prod (fun j _ => RootFieldNumerics.Ii.contDiffOn_zpow_h (ℓ j) (hℓ j) (n j))

theorem comb_a {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ) :
    (combLine ℓ n).a = ∑ j, n j • (ℓ j).a := rfl

theorem exists_smooth (b : K → ℤ) : ∃ B : HermLine ι, IsSmoothHerm B ∧ B.a = b := by
  classical
  let ℓ : K → HermLine ι := fun k =>
    { a := Pi.single k 1
      h := fun z => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2)
      pos := by
        intro z hz
        obtain ⟨i, hi⟩ := hz k
        apply Real.sqrt_pos.mpr
        exact Finset.sum_pos' (fun _ _ => by positivity)
          ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
      smul := by
        intro c z hc
        have hprod : ∏ k', ‖c k'‖ ^ ((Pi.single k (1 : ℤ) : K → ℤ) k') = ‖c k‖ := by
          rw [Fintype.prod_eq_single k]
          · simp
          · intro k' hk'
            simp [Pi.single_apply, hk']
        rw [hprod]
        simp only [norm_mul, mul_pow]
        rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] }
  refine ⟨combLine ℓ b, smooth_comb (fun k => ?_) b, ?_⟩
  · show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (k : K) × ι k → ℂ => Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))
      {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    apply ContDiffOn.sqrt
    · exact (ContDiff.sum (fun i _ => (contDiff_norm_sq ℂ).comp
        (contDiff_apply (𝕜 := ℝ) (E := ℂ) (⟨k, i⟩ : (k : K) × ι k)))).contDiffOn
    · intro z hz
      obtain ⟨i, hi⟩ := hz k
      exact (Finset.sum_pos' (fun _ _ => by positivity)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'
  · rw [comb_a]
    funext k'
    simp [ℓ, Finset.sum_apply, Pi.single_apply]

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa using hX
  · simpa using hL i

theorem last_lin (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (P : Ideal (MRing ι)) (e : ℕ)
    (hP : IsArithVar P (e + 2)) (L : Fin e → HermLine ι) (A B C : HermLine ι) (m : ℤ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (hC : IsSmoothHerm C)
    (hdeg : C.a = B.a + m • A.a) :
    ptsIntegral P (fun j z => Real.log (((Fin.snoc L C : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) =
      ptsIntegral P (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) +
        m * ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z))
          (fun _ => 1) := by
  classical
  let ℓ : Fin e ⊕ Bool → HermLine ι := Sum.elim L (fun t => if t then A else B)
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := by
    rintro (i | _ | _) <;> simp [ℓ, hL, hA, hB]
  let n : Fin (e + 1) → Fin e ⊕ Bool → ℤ :=
    Fin.snoc (fun i => Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr false) 1 + m • Pi.single (Sum.inr true) 1)
  obtain ⟨hexp, hperm⟩ := GlobalTheory.T.log_integral_multilinear II hII K ι P (e + 1) (Fin e ⊕ Bool) ℓ n hP hℓ
  have h1 := hperm (fun k => combLine ℓ (n k)) (Fin.snoc L C) 1 (fun k => smooth_comb hℓ _)
    (smooth_snoc hL hC) (by
      intro k
      simp only [Equiv.Perm.coe_one, id]
      rw [comb_a]
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply, hdeg]
        abel
      · simp [n, ℓ, Fintype.sum_sum_type, Pi.single_apply])
  let w0 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr false)
  let w1 : Fin (e + 1) → Fin e ⊕ Bool := Fin.snoc (fun i => Sum.inl i) (Sum.inr true)
  have hne : w0 ≠ w1 := by
    intro h
    have := congrFun h (Fin.last e)
    simp [w0, w1] at this
  have hzero : ∀ w : Fin (e + 1) → Fin e ⊕ Bool, w ≠ w0 ∧ w ≠ w1 →
      (∏ k, (n k (w k) : ℝ)) * ptsIntegral P (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) = 0 := by
    rintro w ⟨hw0, hw1⟩
    apply mul_eq_zero_of_left
    by_contra hprod
    have hf : ∀ k, (n k (w k) : ℝ) ≠ 0 := fun k =>
      Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ _)
    have hcs : ∀ i : Fin e, w (Fin.castSucc i) = Sum.inl i := by
      intro i
      have := hf (Fin.castSucc i)
      simp [n, Pi.single_apply] at this
      exact this
    have hl := hf (Fin.last e)
    rcases hw : w (Fin.last e) with i | (_ | _)
    · rw [hw] at hl
      simp [n, Pi.single_apply] at hl
    · exact hw0 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w0, hw]
        · simp [w0, hcs i])
    · exact hw1 (funext fun k => by
        refine Fin.lastCases ?_ (fun i => ?_) k
        · simp [w1, hw]
        · simp [w1, hcs i])
  have e0 : ∀ k, ℓ (w0 k) = (Fin.snoc L B : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w0]
  have e1 : ∀ k, ℓ (w1 k) = (Fin.snoc L A : Fin (e + 1) → HermLine ι) k := by
    intro k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp [ℓ, w1]
  have p0 : ∏ k, (n k (w0 k) : ℝ) = 1 := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w0]
  have p1 : ∏ k, (n k (w1 k) : ℝ) = m := by
    rw [Fin.prod_univ_castSucc]
    simp [n, w1]
  rw [h1, hexp, Fintype.sum_eq_add w0 w1 hne hzero, p0, p1]
  simp only [e0, e1, one_mul]

end RootFieldNumerics.EffN
end
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.intersection_section_log_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : Ω), IsArithVar (mCoordIdeal y) (e + 2) → Birational y → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → s ≠ 0 → s ∈ chartLatNm y A.a 1 → (∀ j W', IsArithVar W' 2 → mCoordIdeal y ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral (mCoordIdeal y) (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
  intro hK hEU hDiv II hII K _ ι _ Ω _ y e L A s hV hB hL hA hs hsA hgeo
  have hW : ∀ W : Ideal (MRing ι), IsArithVar W (e + 1) → mCoordIdeal y ≤ W →
      0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    intro W hW hle
    exact GlobalTheory.T.ptsIntegral_log_nonneg hK hEU hDiv II hII K ι W e L hW hL
      (fun j W' hW' hle' => hgeo j W' hW' (le_trans hle hle'))
  obtain ⟨b, c, hc0, hc⟩ := GlobalTheory.T.chart_lattice_power_section K ι Ω y (e + 2) A.a s hV hB hsA
  obtain ⟨B, hBs, hBa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) b
  have key : ∀ n : ℕ, 0 ≤ ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
      + (n : ℝ) * ptsIntegral (mCoordIdeal y)
      (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) := by
    intro n
    obtain ⟨C, hCs, hCa⟩ := RootFieldNumerics.EffN.exists_smooth (ι := ι) (b + n • A.a)
    have hCa' : C.a = B.a + (n : ℤ) • A.a := by rw [hCa, hBa, natCast_zsmul]
    have hmem : c * s ^ n ∈ chartLat y C.a 1 := by rw [hCa]; exact hc n
    have h0 := GlobalTheory.T.arith_intersection_section_recursion II hII hDiv K ι Ω y e L C (c * s ^ n) hV hB hL hCs
      (mul_ne_zero hc0 (pow_ne_zero _ hs)) hmem hW
    rw [RootFieldNumerics.EffN.last_lin II hII (mCoordIdeal y) e hV L A B C (n : ℤ) hL hA hBs hCs hCa'] at h0
    simpa using h0
  set PB := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L B : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  set PA := ptsIntegral (mCoordIdeal y)
    (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1)
  by_contra hneg
  push_neg at hneg
  have hpos : 0 < -PA := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (PB / -PA)
  have h1 := (div_lt_iff₀ hpos).mp hn
  have h2 := key n
  have h3 : (n : ℝ) * -PA = -((n : ℝ) * PA) := by ring
  linarith
end
