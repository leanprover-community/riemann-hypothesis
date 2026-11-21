import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefIdem

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) :
    chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add, add_mul]

private lemma weak (π : Equiv.Perm (Fin (2 + 2))) (ν μ : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν (π i) * (-((i : ℕ) : ℤ)) ≤ ∑ i, μ (π i) * (-((i : ℕ) : ℤ)) := by
  have h1 := h 1 (fun i => -(((π.symm i : Fin (2 + 2)) : ℕ) : ℤ)) (by
    intro a b hab
    simp only [Function.comp_apply, Equiv.symm_apply_apply, neg_le_neg_iff, Nat.cast_le]
    exact hab)
  rw [← Equiv.sum_comp π, ← Equiv.sum_comp π (fun i => μ i * _)] at h1
  simpa only [Equiv.Perm.one_apply, Equiv.symm_apply_apply] using h1

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expMul :
    ∀ π ψ ψ' μ μ', OExp π ψ μ → OExp π ψ' μ' → OExp π (fun k => ψ k * ψ' k) (μ + μ') := by
  rintro π ψ ψ' μ μ' ⟨J, _, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩
    ⟨J', _, j₀', a', b', ν', hc', he', ha', hb', hν', hw', hf, hf'⟩
  refine ⟨J × J', inferInstance, (j₀, j₀'), fun j h => a j.1 h * a' j.2 h, fun j h => b j.1 h * b' j.2 h,
    fun j => ν j.1 + ν' j.2, fun j => ⟨(hc j.1).1.mul (hc' j.2).1, (hc j.1).2.mul (hc' j.2).2⟩,
    fun h k => ?_, ?_, ?_, ?_, fun j θ h => ?_, fun j w y hy => ?_, fun j hj => ?_⟩
  · simp only [he, he', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [ha, ha']
  · simp only [hb, hb']
  · simp only [hν, hν']
  · obtain ⟨h1, h2, h3⟩ := hw j.1 θ h
    obtain ⟨h1', h2', h3'⟩ := hw' j.2 θ h
    simp only [h1, h2, h3, h1', h2', h3', chi_add]
    refine ⟨by ring, by ring, by ring⟩
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_le_add (hg j.1 w y hy) (hf j.2 w y hy)
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    by_cases h1 : j.1 = j₀
    · have h2 : j.2 ≠ j₀' := fun h2 => hj (Prod.ext h1 h2)
      exact add_lt_add_of_le_of_lt (weak π _ _ (hg j.1)) (hf' j.2 h2)
    · exact add_lt_add_of_lt_of_le (hg' j.1 h1) (weak π _ _ (hf j.2))
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem sum_fin_four_expand {M : Type} [AddCommMonoid M] (f : Fin (2 + 2) → M) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private theorem eb_dg (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  u4.2.2.2.2.2.2.2.1 θ

private theorem eb_chi_single (j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) :
    chi (Pi.single j 1) θ = Complex.exp (Complex.I * θ j) := by
  unfold chi
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

private theorem eb_chi_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (-ν) θ = conj (chi ν θ) := by
  unfold chi
  rw [← Complex.exp_conj]
  congr 1
  simp [map_sum]

private theorem eb_right (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (h * dg θ) = chi (Pi.single j 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, mul_diagonal, mul_comm]

private theorem eb_left (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (dg θ * h) = chi (Pi.single i 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, diagonal_mul]

private theorem eb_mul (π : Equiv.Perm (Fin (2 + 2))) (i j : Fin (2 + 2)) (h k : U4) :
    en i j (h * k) = ∑ s, en i (π s) h * en (π s) j k := by
  unfold en
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  exact (Equiv.sum_comp π fun s => (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i s * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) s j).symm

private theorem eb_cont (i j : Fin (2 + 2)) : Continuous (en i j) :=
  (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_elem i j

private theorem eb_pair (j : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) : ∑ i, (Pi.single j 1 : Fin (2 + 2) → ℤ) i * f i = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_pairπ (π : Equiv.Perm (Fin (2 + 2))) (s : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) :
    ∑ i, (Pi.single (π s) 1 : Fin (2 + 2) → ℤ) (π i) * f i = f s := by
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (π.injective.ne hb)]
  · simp

private theorem eb_top (z : Fin (2 + 2) → ℤ) (hz : Antitone z) (s t : Fin (2 + 2)) (hst : s ≠ t) : z s + z t ≤ z 0 + z 1 := by
  have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
  have h1 : ∀ u : Fin (2 + 2), u ≠ 0 → (1 : Fin (2 + 2)) ≤ u := by decide
  by_cases hs : s = 0
  · have ht : t ≠ 0 := fun h => hst (hs.trans h.symm)
    have := hz (h0 s)
    have := hz (h1 t ht)
    omega
  · have := hz (h0 t)
    have := hz (h1 s hs)
    omega

private theorem eb_one (π : Equiv.Perm (Fin (2 + 2))) : OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 0, fun s => en (π 0) (π s), fun s => en (π s) (π 0), fun s => Pi.single (π s) 1,
    fun s => ⟨eb_cont _ _, eb_cont _ _⟩, fun h k => eb_mul π _ _ h k, rfl, rfl, rfl,
    fun s θ h => ⟨eb_right _ _ _ _, eb_left _ _ _ _, eb_left _ _ _ _⟩, fun s w y hy => ?_, fun s hs => ?_⟩
  · rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · beta_reduce
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ)]
    revert s
    decide

private theorem eb_three (π : Equiv.Perm (Fin (2 + 2))) : OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 3, fun s k => conj (en (π 3) (π s) k), fun s k => conj (en (π s) (π 3) k),
    fun s => -Pi.single (π s) 1,
    fun s => ⟨Complex.continuous_conj.comp (eb_cont _ _), Complex.continuous_conj.comp (eb_cont _ _)⟩, fun h k => ?_, rfl, rfl, rfl,
    fun s θ h => ?_, fun s w y hy => ?_, fun s hs => ?_⟩
  · simp only [eb_mul π, map_sum, map_mul]
  · simp only [eb_right, eb_left, eb_chi_neg, map_mul, and_self]
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), u ≤ (3 : Fin (2 + 2)) := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 3 fun i => -(i : ℤ)]
    revert s
    decide

private def ebS : Fin 6 → Fin (2 + 2) := ![0, 0, 0, 1, 1, 2]

private def ebT : Fin 6 → Fin (2 + 2) := ![1, 2, 3, 2, 3, 3]

private theorem eb_two (π : Equiv.Perm (Fin (2 + 2))) :
    OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k)
      (Pi.single (π 0) 1 + Pi.single (π 1) 1) := by
  refine ⟨Fin 6, inferInstance, 0,
    fun p k => en (π 0) (π (ebS p)) k * en (π 1) (π (ebT p)) k - en (π 0) (π (ebT p)) k * en (π 1) (π (ebS p)) k,
    fun p k => en (π (ebS p)) (π 0) k * en (π (ebT p)) (π 1) k - en (π (ebS p)) (π 1) k * en (π (ebT p)) (π 0) k,
    fun p => Pi.single (π (ebS p)) 1 + Pi.single (π (ebT p)) 1,
    fun p => ⟨((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _)),
      ((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _))⟩, fun h k => ?_, rfl, rfl, rfl,
    fun p θ h => ?_, fun p w y hy => ?_, fun p hp => ?_⟩
  · simp only [eb_mul π, sum_fin_four_expand, Fin.sum_univ_six, ebS, ebT, Matrix.cons_val]
    ring
  · simp only [eb_right, eb_left, eb_chi_add]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pair (π (ebS p)) fun i => y (w i), eb_pair (π (ebT p)) fun i => y (w i), eb_pair, eb_pair]
    have hne : ∀ p, ebS p ≠ ebT p := by decide
    simpa using eb_top _ hy (π.symm (w (π (ebS p)))) (π.symm (w (π (ebT p))))
      (π.symm.injective.ne (w.injective.ne (π.injective.ne (hne p))))
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pairπ π (ebS p) fun i => -(i : ℤ), eb_pairπ π (ebT p) fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ),
      eb_pairπ π 1 fun i => -(i : ℤ)]
    revert p
    decide

private theorem eb_det_dg (δ : ℤ) (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ = chi (fun _ => δ) θ := by
  unfold chi
  rw [eb_dg, det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  ring

private theorem eb_four (π : Equiv.Perm (Fin (2 + 2))) (δ : ℤ) :
    OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  have hc : Continuous fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ :=
    (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_det.zpow₀ δ fun k =>
      Or.inl (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  have hm : ∀ h k : U4, ((h * k : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ =
      (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ := fun h k => by
    rw [Submonoid.coe_mul, det_mul, mul_zpow]
  refine ⟨Unit, inferInstance, (), fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ,
    fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ _ => δ, fun _ => ⟨hc, hc⟩, fun h k => ?_, rfl, rfl, rfl,
    fun _ θ h => ?_, fun _ w y _ => ?_, fun _ hs => absurd rfl hs⟩
  · simp only [hm, Finset.univ_unique, Finset.sum_singleton]
  · simp only [hm, eb_det_dg, and_self, and_true]
    exact mul_comm _ _
  · exact (Equiv.sum_comp w fun i => δ * y i).le

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expBasic :
    ∀ π : Equiv.Perm (Fin (2 + 2)), OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) ∧
      OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k) (Pi.single (π 0) 1 + Pi.single (π 1) 1) ∧
      OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) ∧ ∀ δ : ℤ, OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  intro π
  exact ⟨eb_one π, eb_two π, eb_three π, eb_four π⟩
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma sq_sum_le_of_dom (π : Equiv.Perm (Fin (2 + 2))) (μ ν : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν i ^ 2 ≤ ∑ i, μ i ^ 2 := by
  have hm : Monotone ((fun i => -ν i) ∘ Tuple.sort (fun i => -ν i)) := Tuple.monotone_sort _
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (2 + 2)), Monotone ((fun i => -ν i) ∘ τ) := ⟨_, hm⟩
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (2 + 2)), s = τ * π⁻¹ := ⟨_, rfl⟩
  have hanti : Antitone ((fun i => ν (s i)) ∘ π) := by
    intro a b hab
    have := hτ hab
    simp only [Function.comp, neg_le_neg_iff] at this
    simpa [hs, Equiv.Perm.mul_apply] using this
  have h1 := h s⁻¹ (fun i => ν (s i)) hanti
  have h2 : ∑ i, ν i * ν (s (s⁻¹ i)) = ∑ i, ν i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  rw [h2] at h1
  have h3 : ∑ i, ν (s i) ^ 2 = ∑ i, ν i ^ 2 := Equiv.sum_comp s fun i => ν i ^ 2
  have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ μ fun i => ν (s i)
  rw [h3] at h4
  have hA : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨A, hAe⟩ : ∃ A, A = ∑ i, ν i ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBe⟩ : ∃ B, B = ∑ i, μ i ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hCe⟩ : ∃ C, C = ∑ i, μ i * ν (s i) := ⟨_, rfl⟩
  rw [← hAe, ← hCe] at h1
  rw [← hAe, ← hBe, ← hCe] at h4
  rw [← hAe] at hA
  rw [← hBe] at hB
  rw [← hAe, ← hBe]
  rcases hA.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · have h5 : A * A ≤ B * A := by nlinarith
    exact le_of_mul_le_mul_right h5 h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expNorm :
    ∀ π ψ μ, OExp π ψ μ → WExp ψ μ := by
  intro π ψ μ h
  obtain ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩ := h
  refine ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, fun j => sq_sum_le_of_dom π μ (ν j) (hg j), ?_⟩
  intro j hj hEq
  have := hg' j hj
  rw [hEq] at this
  exact lt_irrefl _ this
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private lemma oexp_pow (π : Equiv.Perm (Fin (2 + 2))) (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) (h : OExp π ψ μ) (n : ℕ) :
    OExp π (fun k => ψ k ^ n) (n • μ) := by
  induction n with
  | zero =>
    have h0 := (expBasic π).2.2.2 0
    simp only [zpow_zero] at h0
    simp only [pow_zero, zero_smul]
    exact h0
  | succ n ih =>
    have h1 := expMul π _ _ _ _ ih h
    simp only [pow_succ, succ_nsmul]
    exact h1

private noncomputable def F (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) : ℂ :=
  en i i k ^ α * (en i i k * en j j k - en i j k * en j i k) ^ β * conj (en l l k) ^ γ *
    (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ

private lemma F_exp (π : Equiv.Perm (Fin (2 + 2))) (i j l : Fin (2 + 2)) (hi : π 0 = i) (hj : π 1 = j) (hl : π 3 = l)
    (α β γ : ℕ) (δ : ℤ) (μ : Fin (2 + 2) → ℤ)
    (hμ : μ = α • (Pi.single i 1 : Fin (2 + 2) → ℤ) + β • (Pi.single i 1 + Pi.single j 1) + γ • (-Pi.single l 1) + fun _ => δ) :
    WExp (F i j l α β γ δ) μ := by
  subst hi hj hl hμ
  obtain ⟨h1, h2, h3, h4⟩ := expBasic π
  exact expNorm π _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (oexp_pow π _ _ h1 α) (oexp_pow π _ _ h2 β))
    (oexp_pow π _ _ h3 γ)) (h4 δ))

private lemma en_inv (i j : Fin (2 + 2)) (k : U4) : en i j k⁻¹ = conj (en j i k) := rfl

private lemma F_star (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) :
    F i j l α β γ δ k⁻¹ = conj (F i j l α β γ δ k) := by
  have hd : ((k⁻¹ : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det = conj ((k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det) := by
    change (star (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ)).det = _
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl
  simp only [F, en_inv, hd, map_mul, map_pow, map_zpow₀, map_sub]
  ring

private lemma en_bd (i j : Fin (2 + 2)) (a b : U2) : en i j (bd a b) =
    fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  unfold en
  rw [u4.1 a b]
  rfl

private lemma det_bd (a b : U2) : (bd a b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det =
    (a : Matrix (Fin 2) (Fin 2) ℂ).det * (b : Matrix (Fin 2) (Fin 2) ℂ).det := by
  rw [u4.1 a b, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

private lemma s0 : (finSumFinEquiv.symm (0 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
private lemma s1 : (finSumFinEquiv.symm (1 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
private lemma s2 : (finSumFinEquiv.symm (2 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
private lemma s3 : (finSumFinEquiv.symm (3 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide

private lemma unitary_two_conj_entry_eq (m : U2) : conj ((m : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
    (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((m : Matrix (Fin 2) (Fin 2) ℂ).det)⁻¹ := by
  have hd := det_ne_zero_of_U2 m
  have h : star (m : Matrix (Fin 2) (Fin 2) ℂ) * (m : Matrix (Fin 2) (Fin 2) ℂ) = 1 := m.2.1
  have h0 := congrFun (congrFun h 1) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h0 h1
  rw [eq_mul_inv_iff_mul_eq₀ hd, Matrix.det_fin_two]
  linear_combination ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * h1 - ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * h0

private lemma c1 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α) (hq : q = β + δ)
    (hn' : n' = γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 1 ∧ π 3 = 3 := by decide
  refine ⟨F 0 1 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c2 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β) (hq : q = δ)
    (hn' : n' = β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 3 := by decide
  refine ⟨F 0 2 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c3 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β + γ) (hq : q = δ - γ)
    (hn' : n' = β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 1 := by decide
  refine ⟨F 0 2 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c4 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β) (hq : q = δ)
    (hn' : n' = α + β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 3 := by decide
  refine ⟨F 2 0 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c5 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β + γ) (hq : q = δ - γ)
    (hn' : n' = α + β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 1 := by decide
  refine ⟨F 2 0 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c6 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = γ) (hq : q = δ - γ)
    (hn' : n' = α) (hq' : q' = β + δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 3 ∧ π 3 = 1 := by decide
  refine ⟨F 2 3 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefEx :
    ∀ n q n' q', ∃ ψ, Coef ψ n q n' q' := by
  intro n q n' q'
  by_cases h1 : (n' : ℤ) + q' ≤ q
  · exact c1 n (q - n' - q').toNat n' (n' + q') n q n' q' rfl (by omega) rfl (by omega)
  by_cases h2 : (n : ℤ) + q ≤ q'
  · exact c6 n' (q' - n - q).toNat n (n + q) n q n' q' rfl (by omega) rfl (by omega)
  by_cases h3 : (n' : ℤ) + q' ≤ n + q
  · by_cases h4 : q' ≤ q
    · exact c2 (n + q - n' - q').toNat (n' + q' - q).toNat (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c3 (n + q - n' - q').toNat n' (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
  · by_cases h4 : q' ≤ q
    · exact c4 (n' + q' - n - q).toNat n (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c5 (n' + q' - n - q).toNat (n + q - q').toNat (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem pw2 {f : U2 → ℂ} (hf : Continuous f)
    (h : ∀ (n : ℕ) (q : ℤ) (l r : U2), ∫ m, conj (KT.psi n q n m) * f (l * m * r) ∂μK = 0) : f = 0 := by
  have key : (fun k => conj (f k)) = 0 := by
    refine PW.eq_zero_of_forall_integral_coeff (Complex.continuous_conj.comp hf) fun n q l₁ l₂ => ?_
    have h1 := h n q l₁⁻¹ l₂⁻¹
    rw [← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂] at h1
    have h2 := congrArg conj h1
    rw [← integral_conj, map_zero] at h2
    have hne : ((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q * (l₂ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 _)) (zpow_ne_zero _ (det_ne_zero_of_U2 _))
    apply mul_left_cancel₀ hne
    rw [mul_zero, ← integral_const_mul, ← h2]
    congr 1; funext k
    have e : l₁⁻¹ * (l₁ * (k * l₂)) * l₂⁻¹ = k := by group
    rw [e, map_mul, starRingEnd_self_apply, ← mul_assoc l₁, KT.psi_mul_mul]
    ring
  funext k
  simpa using congrFun key k

private theorem int2 {f : U2 × U2 → ℂ} (hf : Continuous f) : Integrable f (μK.prod μK) :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

private theorem tor2 (n₁ : ℕ) (q₁ : ℤ) (n₂ : ℕ) (q₂ : ℤ) (ν : Fin (2 + 2) → ℤ) (b : U4 → ℂ)
    (hb : ∀ θ h, b (dg θ * h) = chi ν θ * b h) (hν : ν ≠ wt n₁ q₁ n₂ q₂) (g : U4) :
    ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g) ∂(μK.prod μK) = 0 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, hdg, -, hchi, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  by_contra hI
  refine hν (hchi _ _ fun θ => ?_)
  apply mul_right_cancel₀ hI
  conv_rhs => rw [← integral_mul_left_eq_self _ ((tC (θ 0) (θ 1), tC (θ 2) (θ 3)) : U2 × U2)]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext p
  have hθ : θ = ![θ 0, θ 1, θ 2, θ 3] := by
    funext i; fin_cases i <;> rfl
  have e : bd (tC (θ 0) (θ 1) * p.1) (tC (θ 2) (θ 3) * p.2) * g = dg θ * (bd p.1 p.2 * g) := by
    rw [← hmul, ← hdg, ← hθ, mul_assoc]
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [e, hb, KT.psi_tC_mul n₁ q₁ le_rfl, KT.psi_tC_mul n₂ q₂ le_rfl, map_mul, map_mul]
  have hc : chi (wt n₁ q₁ n₂ q₂) θ * (conj (Complex.exp (Complex.I * ((((n₁ : ℝ) + q₁) * θ 0 + ((n₁ : ℝ) - n₁ + q₁) * θ 1 : ℝ) : ℂ))) *
      conj (Complex.exp (Complex.I * ((((n₂ : ℝ) + q₂) * θ 2 + ((n₂ : ℝ) - n₂ + q₂) * θ 3 : ℝ) : ℂ)))) = 1 := by
    rw [chi, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    have hs : ∑ i, ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ) =
        ((n₁ : ℂ) + q₁) * θ 0 + q₁ * θ 1 + ((n₂ : ℂ) + q₂) * θ 2 + q₂ * θ 3 := by
      have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ))
      refine this.trans ?_
      simp [wt]
    rw [hs]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  linear_combination (-(chi ν θ * conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g))) * hc

private theorem wt_eq {n : ℕ} {q : ℤ} {n' : ℕ} {q' : ℤ} {n₁ : ℕ} {q₁ : ℤ} {n₂ : ℕ} {q₂ : ℤ} (h₁ : Above n q n₁ q₁)
    (h₂ : Above n' q' n₂ q₂) (h : ∑ i, wt n₁ q₁ n₂ q₂ i ^ 2 ≤ ∑ i, wt n q n' q' i ^ 2) : wt n₁ q₁ n₂ q₂ = wt n q n' q' := by
  have hs : ∀ (a : ℕ) (b : ℤ) (c : ℕ) (d : ℤ), ∑ i, wt a b c d i ^ 2 = (a + b) ^ 2 + b ^ 2 + (c + d) ^ 2 + d ^ 2 := by
    intro a b c d
    refine (Fin.sum_univ_four (fun i : Fin 4 => wt a b c d i ^ 2)).trans ?_
    simp [wt]
  rw [hs, hs] at h
  obtain ⟨a1, a2⟩ := h₁
  obtain ⟨b1, b2⟩ := h₂
  have a1' : (n : ℤ) ≤ n₁ := by exact_mod_cast a1
  have b1' : (n' : ℤ) ≤ n₂ := by exact_mod_cast b1
  have hn : (0 : ℤ) ≤ n := by positivity
  have hn' : (0 : ℤ) ≤ n' := by positivity
  have e : ∀ a b : ℤ, 2 * ((a + b) ^ 2 + b ^ 2) = (a + 2 * b) ^ 2 + a ^ 2 := by intros; ring
  have e1 := e n₁ q₁
  have e2 := e n₂ q₂
  have e3 := e n q
  have e4 := e n' q'
  rw [a2] at e1
  rw [b2] at e2
  have s1 : (n : ℤ) ^ 2 ≤ (n₁ : ℤ) ^ 2 := by gcongr
  have s2 : (n' : ℤ) ^ 2 ≤ (n₂ : ℤ) ^ 2 := by gcongr
  have t1 : (n₁ : ℤ) = n := (pow_left_inj₀ (by omega) hn two_ne_zero).1 (by linarith)
  have t2 : (n₂ : ℤ) = n' := (pow_left_inj₀ (by omega) hn' two_ne_zero).1 (by linarith)
  have u1 : q₁ = q := by omega
  have u2 : q₂ = q' := by omega
  simp only [wt, t1, t2, u1, u2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefInj :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ →
      LAbove (fun m => bd m 1) n q Φ → LAbove (fun m => bd 1 m) n' q' Φ → (∀ a b, Φ (bd a b) = 0) → Φ = 0 := by
  intro μ ψ n q n' q' hμ _ hψ Φ hΦ hfix hL hR h0
  obtain ⟨-, hmul, hone, -, hcont, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha0, hb0, hν0, htor, hgood, hgood'⟩ := hψ.exp
  haveI := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun k => (hμ.left k).map_eq⟩
  have int4 : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  set c : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ with hcdef
  have hrep : ∀ g, Φ g = ∫ k, c * ψ (k⁻¹ * g) * Φ k ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self _ g, ← hfix g]
    congr 1; funext k
    have e : (g * k)⁻¹ * g = k⁻¹ := by group
    rw [e, hψ.star, eOf]
  have hsum : ∀ h x, Φ (h * x) = ∑ j, (∫ k, c * a j (k⁻¹ * h) * Φ k ∂μ) * b j x := by
    intro h x
    rw [hrep]
    simp_rw [← integral_mul_const]
    rw [← integral_finset_sum]
    · congr 1; funext k
      rw [← mul_assoc, hexp, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro j _
      have := (hc j).1
      exact int4 _ (by fun_prop)
  have hp := fun m r => KT.continuous_conj_psi m r m
  have hbd : ∀ l l' : U2, Continuous fun p : U2 × U2 => bd (l * p.1) (l' * p.2) := fun l l' =>
    hcont.comp (f := fun p : U2 × U2 => (l * p.1, l' * p.2)) (by fun_prop)
  have hint : ∀ n₁ q₁ n₂ q₂ l l' g, Integrable (fun p : U2 × U2 => conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g)) (μK.prod μK) := fun n₁ q₁ n₂ q₂ l l' g =>
    int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
      (hΦ.comp ((hbd l l').mul continuous_const)))
  have main : ∀ n₁ q₁ n₂ q₂ l l' g, ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g) ∂(μK.prod μK) = 0 := by
    intro n₁ q₁ n₂ q₂ l l' g
    by_cases h₁ : Above n q n₁ q₁
    · by_cases h₂ : Above n' q' n₂ q₂
      · simp_rw [← hmul l l', mul_assoc (bd l l'), hsum (bd l l'), Finset.mul_sum]
        rw [integral_finset_sum]
        · refine Finset.sum_eq_zero fun j _ => ?_
          simp_rw [mul_left_comm _ (∫ k, c * a j (k⁻¹ * bd l l') * Φ k ∂μ)]
          rw [integral_const_mul]
          by_cases hj : j = j₀
          · rw [hj, ha0, ← hrep, h0, zero_mul]
          · rw [tor2 n₁ q₁ n₂ q₂ (ν j) (b j) (fun θ h => (htor j θ h).2.2), mul_zero]
            intro hν
            have h3 := hgood j
            simp only [hν] at h3
            exact hgood' j hj (hν.trans (wt_eq h₁ h₂ h3))
        · intro j _
          exact int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
            (continuous_const.mul ((hc j).2.comp (hcont.mul continuous_const))))
      · rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' g)]
        refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
        have h3 := hR n₂ q₂ h₂ l' (bd (l * x) 1 * g)
        simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
        simp only [mul_assoc (conj (KT.psi n₁ q₁ n₁ x))]
        rw [integral_const_mul, h3, mul_zero]
    · rw [integral_prod_symm _ (hint n₁ q₁ n₂ q₂ l l' g)]
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
      have h3 := hL n₁ q₁ h₁ l (bd 1 (l' * x) * g)
      simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
      simp only [mul_comm _ (conj (KT.psi n₂ q₂ n₂ x)), mul_assoc (conj (KT.psi n₂ q₂ n₂ x))]
      rw [integral_const_mul, h3, mul_zero]
  have step : ∀ n₂ q₂ l' g, (fun x => ∫ y, conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g) ∂μK) = 0 := by
    intro n₂ q₂ l' g
    refine pw2 ?_ fun n₁ q₁ l r => ?_
    · have h3 := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun x y : U2 => conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g))
        (((hp _ _).comp continuous_snd).mul (hΦ.comp ((by simpa using hbd 1 l' : Continuous fun p : U2 × U2 => bd p.1 (l' * p.2)).mul
          continuous_const))) isCompact_univ
      simpa only [Measure.restrict_univ] using h3
    · have h3 := main n₁ q₁ n₂ q₂ l l' (bd r 1 * g)
      rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' _)] at h3
      rw [← h3]
      congr 1; funext x
      rw [← integral_const_mul]
      congr 1; funext y
      simp only [← mul_assoc, hmul, mul_one]
  funext g
  have fin : (fun y => Φ (bd 1 y * g)) = 0 := by
    refine pw2 (hΦ.comp ((hcont.comp (f := fun y : U2 => ((1 : U2), y)) (by fun_prop)).mul continuous_const)) fun n₂ q₂ l r => ?_
    have h3 := congrFun (step n₂ q₂ l (bd 1 r * g)) 1
    simpa only [← mul_assoc, hmul, mul_one, Pi.zero_apply] using h3
  simpa [hone] using congrFun fin 1
end

section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.ext4 :
    ∀ (μ : Measure U4), Haar4 μ → μ.IsOpenPosMeasure → ∀ n q n' q', ∃ e, Ext μ e n q n' q' 1 ∧ Ext μ e n' q' n q w4 := by
  intro μ hμ hpos n q n' q'
  obtain ⟨ψ, hψ⟩ := coefEx n q n' q'
  obtain ⟨hc, -, hidem, hfix⟩ := coefIdem μ ψ n q n' q' hμ hpos hψ
  have hF := coefFix μ ψ n q n' q' hμ hpos hψ
  have hI := coefInj μ ψ n q n' q' hμ hpos hψ
  obtain ⟨-, -, -, -, -, hww, hwb, -⟩ := u4
  have hsc : ∀ (c : ℂ) (x : U4), RFix μ (eOf μ ψ) (fun k => c * ψ (x * k)) := by
    intro c x g
    have h := hfix (x * g)
    show ∫ k, eOf μ ψ k * (c * ψ (x * (g * k))) ∂μ = c * ψ (x * g)
    rw [← h, ← integral_const_mul]
    congr 1
    funext k
    rw [mul_assoc x g k]
    ring
  have hcc : ∀ (c : ℂ) (x : U4), Continuous (fun k => c * ψ (x * k)) := fun c x =>
    continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  refine ⟨eOf μ ψ, ⟨hidem, ?_, ?_, ?_⟩, ⟨hidem, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ hR g
    simpa only [mul_one] using hF Φ hΦ hR g
  · intro Φ hΦ hR h1 h2 h0
    exact hI Φ hΦ hR h1 h2 (by simpa only [mul_one] using h0)
  · refine ⟨_, hcc (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((KT.normSqInt n' q' : ℝ) : ℂ)⁻¹) 1, hsc _ 1, ?_⟩
    intro a b
    simp only [mul_one, one_mul, hψ.res, T, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · intro Φ hΦ hR g
    obtain ⟨h1, h2⟩ := hF Φ hΦ hR (g * w4)
    refine ⟨?_, ?_⟩
    · rw [← h2]
      congr 1
      funext m
      rw [mul_assoc g w4, hwb, mul_assoc g]
    · rw [← h1]
      congr 1
      funext m
      rw [mul_assoc g w4, hwb, mul_assoc g]
  · intro Φ hΦ hR h1 h2 h0
    have key : (fun k => Φ (w4 * k)) = 0 := by
      refine hI _ (hΦ.comp (continuous_const.mul continuous_id)) ?_ ?_ ?_ ?_
      · intro g
        have h := hR (w4 * g)
        simpa only [mul_assoc] using h
      · intro N Q hN l k
        have h := h2 N Q hN l (w4 * k)
        simpa only [← mul_assoc w4, hwb, ← mul_assoc (bd _ _) w4] using h
      · intro N Q hN l k
        have h := h1 N Q hN l (w4 * k)
        simpa only [← mul_assoc w4, hwb, ← mul_assoc (bd _ _) w4] using h
      · intro a b
        show Φ (w4 * bd a b) = 0
        rw [hwb]
        exact h0 b a
    funext k
    have h := congrFun key (w4 * k)
    simpa only [← mul_assoc, hww, one_mul, Pi.zero_apply] using h
  · refine ⟨_, hcc (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((KT.normSqInt n' q' : ℝ) : ℂ)⁻¹) w4, hsc _ w4, ?_⟩
    intro a b
    have e : w4 * (bd a b * w4) = bd b a := by
      rw [← mul_assoc, hwb, mul_assoc, hww, mul_one]
    simp only [e, hψ.res, T, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    ring
end
