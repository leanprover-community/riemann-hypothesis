import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.AnalyticAtTsum
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.BcSumD
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.NeZeroOne
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.GaloisGenerators.LocRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.QuadOf
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftSum
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.LiftPow

section
open UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux in
theorem UpperTheory.ConvolutionTheory.R.zeroExp :
    ZeroExp := by
  classical
  intro W q X d A hS ι _ x hw hsm
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  have hq := hS.primes.two
  have hC := UpperTheory.ConvolutionTheory.Rs.conv1 W q X d A hS
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => (x i).2) ⟨i₁, Finset.mem_univ _⟩
  set m : ℝ := (x i₀).2 with hm
  have ht : ∀ i, m ≤ (x i).2 := fun i => hi₀ i (Finset.mem_univ _)
  have hm0 : m < 0 := by
    by_contra h
    push Not at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Nat.cast_nonneg (d (x i).1)) (h.trans (ht i)))).1 hw i₁ (Finset.mem_univ _)
    rcases mul_eq_zero.1 h1 with h2 | h2
    · have := hS.pos (x i₁).1
      have h3 : d (x i₁).1 = 0 := by exact_mod_cast h2
      omega
    · exact hi₁ h2
  set α : W → (Σ i, Fin (d (x i).1)) → ℂ :=
    fun w a => A (x a.1).1 w a.2 * (q w : ℂ) ^ (-((x a.1).2 : ℂ)) with hα
  have hxx : ∀ (σ : ℝ) (p : W × ℕ),
      ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p = lterm q α α σ p := fun σ p => by
    rw [sum_lterm q hq A x x σ p]
    simp only [lterm, Pw, hα, Fintype.sum_sigma]
  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2 - m) (fun i => (x i).2 ≠ m)
    (fun i hi => sub_pos.2 (lt_of_le_of_ne (ht i) (Ne.symm hi)))
  choose M hM using fun i i' : ι => (hC (x i).1 (x i').1).2 (1 + τ) (by linarith)
  have : Nonempty {i // (x i).2 = m} := ⟨⟨i₀, rfl⟩⟩
  refine UpperTheory.ConvolutionTheory.Rs.unb W q X d A hS {i // (x i).2 = m} (fun i => (x i.1).1)
    ⟨(∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => ((hC _ _).1 _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ - 2 * m + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, show σ - 2 * m + m + m = σ by ring]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = _ := tsum_congr fun p => hxx _ p
  rw [hform, dsum_subtype (fun i => (x i).2 = m)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ :=
    fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ - 2 * m + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : ‖∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p‖ ≤ ∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖ :=
    tsum_of_norm_bounded (hsm (1 - 2 * m) (by linarith)).hasSum fun p =>
      DiagonalEntryNormBounds.norm_lterm_anti q hq α α (by linarith) p
  have heq : (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) =
      (∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p) -
        ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hDle hrest)
end

section
noncomputable section

open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.R.Ac2

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs

theorem ps {ι M : Type} [Fintype ι] [AddCommMonoid M] {d : ι → ℕ} {m : ℕ} {g : ∀ i, Fin (d i) → ℂ} {h : Fin m → ℂ}
    (e : ∑ i, Finset.univ.val.map (g i) = Finset.univ.val.map h) (φ : ℂ → M) : ∑ i, ∑ a, φ (g i a) = ∑ a, φ (h a) := by
  have := congrArg (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom φ)) e
  rw [map_sum] at this
  have e1 : ∀ {n : ℕ} (k : Fin n → ℂ), (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom φ)) (Finset.univ.val.map k) =
      ∑ a, φ (k a) := fun k => congrArg Multiset.sum (Multiset.map_map φ k Finset.univ.val)
  simpa only [e1] using this

theorem logsum {m : ℕ} {a : Fin m → ℂ} (h : ‖∏ i, a i‖ = 1) (q f : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    ∑ i, Real.log ‖(a i * (q : ℂ) ^ (-(t : ℂ))) ^ f‖ = f * m * (-t * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hne : ∀ i, ‖a i‖ ≠ 0 := fun i hi => by
    rw [norm_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi] at h
    exact zero_ne_one h
  have hs : ∑ i, Real.log ‖a i‖ = 0 := by
    rw [← Real.log_prod fun i _ => hne i, ← norm_prod, h, Real.log_one]
  have e : ∀ i, Real.log ‖(a i * (q : ℂ) ^ (-(t : ℂ))) ^ f‖ = f * (Real.log ‖a i‖ + -t * Real.log q) := fun i => by
    rw [norm_pow, Real.log_pow, norm_mul, Common0Aux.cpow_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_pos_of_pos h0 _).le, Real.log_mul (hne i) (Real.rpow_pos_of_pos h0 _).ne',
      Real.log_rpow h0]
  simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem shift (q : ℕ) (hq : 2 ≤ q) (s t : ℝ) :
    (q : ℂ) ^ (-(s : ℂ)) * (q : ℂ) ^ (-((-t : ℝ) : ℂ)) = (q : ℂ) ^ (-((s - t : ℝ) : ℂ)) := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast (by omega : q ≠ 0))]
  congr 1
  push_cast
  ring

theorem cancel (q f : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    ((q : ℂ) ^ (-(t : ℂ))) ^ f * ((q ^ f : ℕ) : ℂ) ^ (-((-t : ℝ) : ℂ)) = 1 := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Common0Aux.cpow_real, Common0Aux.cpow_real, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Nat.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_mul h0.le, ← Real.rpow_add h0]
  simp [mul_comm]

theorem eq_of_bdd (N N' : ℕ) (C : ℝ) (h : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → |((N : ℝ) - N') * (-Real.log (σ - 1))| ≤ C) : N = N' := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 2 one_lt_two le_rfl)
  have h1 := h (1 + Real.exp (-(C + 1))) (by linarith [Real.exp_pos (-(C + 1))])
    (by linarith [Real.exp_le_one_iff.2 (show -(C + 1) ≤ 0 by linarith)])
  rw [add_sub_cancel_left, Real.log_exp, neg_neg, abs_mul, abs_of_nonneg (show 0 ≤ C + 1 by linarith)] at h1
  by_contra hne
  have h2 : (1 : ℤ) ≤ |(N : ℤ) - N'| := Int.one_le_abs (by omega)
  have h3 : (1 : ℝ) ≤ |(N : ℝ) - N'| := by exact_mod_cast h2
  nlinarith

theorem sum_bd {I : Type} (s : Finset I) (P : I → Prop) [DecidablePred P] (a M : I → ℝ) (L : ℝ)
    (h : ∀ i, |a i - (if P i then L else 0)| ≤ M i) : |∑ i ∈ s, a i - (s.filter P).card * L| ≤ ∑ i ∈ s, M i := by
  have e : ((s.filter P).card : ℝ) * L = ∑ i ∈ s, if P i then L else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [e, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

end UpperTheory.ConvolutionTheory.R.Ac2

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs Ac2

theorem absCount2 : BCSum → ZeroExp → LogAsym → AbsCount := by
  intro hB hZ hL l W W' q q' u f c hl hC X X' d d' A A' hS hS' ι _ x y z t t' hy h1 h2
  classical
  have hq := hS.primes.two
  have hq' := hS'.primes.two
  have hq1 : ∀ v, 1 ≤ q v := fun v => le_trans one_le_two (hq v)
  obtain ⟨w₀⟩ : Nonempty W' := by
    by_contra hn
    have := not_nonempty_iff.1 hn
    exact hS'.primes.div Summable.of_finite
  have key : ∀ (x : X) (t : ℝ), (∀ w, ∑ i, Finset.univ.val.map (fun a => A' (z i).1 w a * (q' w : ℂ) ^ (-((z i).2 : ℂ))) =
      Finset.univ.val.map fun a => (A x (u w) a * (q (u w) : ℂ) ^ (-(t : ℂ))) ^ f w) →
      ∑ i, (d' (z i).1 : ℝ) = d x ∧ ∑ i, (d' (z i).1 : ℝ) * (z i).2 = d x * t ∧ ∀ w (k : ℕ),
        ∑ a : Σ i, Fin (d' (z i).1), (A' (z a.1).1 w a.2 * (q' w : ℂ) ^ (-(((z a.1).2 - t : ℝ) : ℂ))) ^ k =
          ∑ a, A x (u w) a ^ (f w * k) := fun x t h => by
    refine ⟨by simpa using ps (h w₀) fun _ => (1 : ℝ), ?_, fun w k => ?_⟩
    · have e := ps (h w₀) fun ζ => Real.log ‖ζ‖
      rw [logsum (hS.det x _) _ _ (hq _)] at e
      have e' : ∀ i, ∑ a, Real.log ‖A' (z i).1 w₀ a * (q' w₀ : ℂ) ^ (-((z i).2 : ℂ))‖ =
          -Real.log (q' w₀) * ((d' (z i).1 : ℝ) * (z i).2) := fun i => by
        have := logsum (hS'.det (z i).1 w₀) _ 1 (hq' w₀) (z i).2
        simp only [pow_one] at this
        rw [this]
        push_cast
        ring
      have hlog : Real.log (q' w₀) = f w₀ * Real.log (q (u w₀)) := by rw [hC.norm, Nat.cast_pow, Real.log_pow]
      have hpos : 0 < Real.log (q' w₀) := Real.log_pos (by exact_mod_cast hq' w₀)
      simp only [e', ← Finset.mul_sum] at e
      refine mul_left_cancel₀ (neg_ne_zero.2 hpos.ne') (e.trans ?_)
      rw [hlog]
      ring
    · have e := ps (h w) fun ζ => (ζ * (q' w : ℂ) ^ (-((-t : ℝ) : ℂ))) ^ k
      rw [Fintype.sum_sigma]
      simp only [mul_assoc, shift _ (hq' w)] at e
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_pow (A x (u w) a), mul_assoc, hC.norm w, cancel _ _ (hq _), mul_one, pow_mul]
  obtain ⟨c1, s1, p1⟩ := key x t h1
  obtain ⟨c2, s2, p2⟩ := key (y 0) t' h2
  have htt : t = t' := by
    have hd : (0 : ℝ) < d x := by exact_mod_cast hS.pos x
    refine mul_left_cancel₀ hd.ne' ?_
    rw [← s1, s2, ← c2, c1]
  subst htt
  have hs : ∀ i, (z i).2 = t := fun i => sub_eq_zero.1 (hZ W' q' X' d' A' hS' ι (fun i => ((z i).1, (z i).2 - t))
    (by simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c1, s1, sub_self])
    (fun σ hσ => (hB l W W' q q' u f c hl hq1 hC _ _ _ _ (A x) (A x) _ _ σ p1 p1 ((conv1 W q X d A hS x x).1 σ hσ)).1) i)
  refine ⟨rfl, hs, ?_⟩
  simp only [hs, sub_self, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at p1 p2
  choose M hM using fun j => hL W q X d A hS x (y j)
  choose M' hM' using fun p : ι × ι => hL W' q' X' d' A' hS' (z p.1).1 (z p.2).1
  refine eq_of_bdd _ _ (∑ j ∈ Finset.range l, M j + ∑ p, M' p) fun σ a b => ?_
  have e := (hB l W W' q q' u f c hl hq1 hC _ _ _ _ (A x) (A (y 0)) _ _ σ p1 p2 ((conv1 W q X d A hS x (y 0)).1 σ a)).2
  have eR : ∀ j p, lterm q (A x) (fun v b => A (y 0) v b * c v ^ j) σ p = lterm q (A x) (A (y j)) σ p := fun j p => by
    have := congrArg (fun m : Multiset ℂ => (m.map (· ^ (p.2 + 1))).sum) (hy j p.1)
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] at this
    simp only [lterm, this]
  have eL : ∀ p, lterm q' (fun w (a : Σ i, Fin (d' (z i).1)) => A' (z a.1).1 w a.2)
      (fun w (a : Σ i, Fin (d' (z i).1)) => A' (z a.1).1 w a.2) σ p =
        ∑ r : ι × ι, lterm q' (A' (z r.1).1) (A' (z r.2).1) σ p := fun p => by
    simp only [lterm, Fintype.sum_sigma, Fintype.sum_prod_type]
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_mul, Finset.sum_div]
  simp only [eR, eL] at e
  rw [Summable.tsum_finsetSum fun r _ => ((conv1 W' q' X' d' A' hS' _ _).1 σ a).of_norm] at e
  have e2 : ∑ r : ι × ι, dre q' (A' (z r.1).1) (A' (z r.2).1) σ = ∑ j ∈ Finset.range l, dre q (A x) (A (y j)) σ := by
    simpa only [Complex.re_sum, dre] using congrArg Complex.re e
  have b1 := abs_le.1 (sum_bd (Finset.range l) (fun j => x = y j) _ M _ fun j => by convert hM j σ a b)
  have b2 := abs_le.1 (sum_bd Finset.univ (fun p : ι × ι => (z p.1).1 = (z p.2).1) _ M' _ fun p => by convert hM' p σ a b)
  rw [e2] at b2
  rw [sub_mul]
  exact abs_le.2 ⟨by linarith [b1.1, b1.2, b2.1, b2.2], by linarith [b1.1, b1.2, b2.1, b2.2]⟩

end UpperTheory.ConvolutionTheory.R
end
end

section
noncomputable section

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs


theorem logAsym : LogAsym := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  have hn := exp_re hS x y F σ₀ hF he
  have h0 : ∀ t ∈ Set.Icc (1 : ℝ) 2, ‖F t‖ ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simpa using ne_zero_one hS x y F σ₀ hF he
    · rw [hn t h]
      refine mul_ne_zero ?_ (Real.exp_pos _).ne'
      split_ifs
      · linarith
      · exact one_ne_zero
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := ContinuousOn.log (fun t ht =>
    ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ))
      Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt) h0
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h := hM σ ⟨h1.le, h2⟩
  rw [hn σ h1, Real.norm_eq_abs] at h
  unfold dre
  split_ifs at h ⊢
  · rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h
    rwa [sub_neg_eq_add, add_comm]
  · rwa [one_mul, Real.log_exp, ← sub_zero (Complex.re _)] at h

end UpperTheory.ConvolutionTheory.R
end
end

section
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual

section

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem normV_inertia (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem unram_ae : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
    ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hfin : {w : HeightOneSpectrum (𝓞 M) | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine Filter.eventually_cofinite.2 ((hfin.image fun w => w.under (𝓞 K)).subset ?_)
  intro v hv
  by_contra hn
  refine hv fun w hw => ?_
  have := w.isPrime
  have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 M) := fun h => hn ⟨w, h, hw⟩
  exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

private theorem card_fibre (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = (v.asIdeal.primesOver (𝓞 M)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩) ⟨fun a b h => ?_, fun P => ?_⟩)
  · exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · obtain ⟨P, hP, hPv⟩ := P
    exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      HeightOneSpectrum.ext hPv.over.symm⟩, rfl⟩

end

theorem UpperTheory.ConvolutionTheory.R.decomp :
    Decomp := by
  intro K M _ _ _ _ _ _ _ _ hl
  filter_upwards [unram_ae K M] with v hv
  have := v.isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  obtain ⟨⟨P, hP, hPv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 M)))
  have he : v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P Gal(M/K)]
    exact hv ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩ (HeightOneSpectrum.ext hPv.over.symm)
  have hn : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v →
      normV w = normV v ^ v.asIdeal.inertiaDegIn (𝓞 M) := by
    rintro w rfl
    have := w.isPrime
    have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
    rw [Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K)]
    exact normV_inertia K M w
  rw [he, one_mul, IsGalois.card_aut_eq_finrank, ← card_fibre] at hfund
  rcases hl.eq_one_or_self_of_dvd _ (Dvd.intro_left _ hfund) with h | h
  · rw [h, mul_one] at hfund
    exact Or.inl ⟨hfund, fun w hw => by rw [hn w hw, h, pow_one]⟩
  · rw [h] at hfund
    exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hl.pos (hfund.trans (one_mul _).symm),
      fun w hw => by rw [hn w hw, h]⟩
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep PositivityTheory.RgJS PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

namespace Pb2

theorem val_pow {E : Type} [Field E] [NumberField E] (η : HChar E) (j : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (η ^ j).val v = η.val v ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem bd {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {π : CG E n} (hπ : π.IsUnitary)
    {S : Finset (HeightOneSpectrum (𝓞 E))} {α : Off E S → Fin n → ℂˣ} (hα : SatOff π S α) (v : Off E S) (a : Fin n) :
    ‖(α v a : ℂ)‖ ≤ Real.sqrt (nq v) := by
  rw [Real.sqrt_eq_rpow]
  exact (PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E n π hπ v.1 _ (hα v) (α v a) (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2.le

theorem fam {n f q q' : ℕ} {A α : Fin n → ℂˣ} (h : Finset.univ.val.map A = Finset.univ.val.map fun a => α a ^ f)
    (hq : q' = q ^ f) (hα : ∀ a, ‖(α a : ℂ)‖ ≤ Real.sqrt q) :
    (∀ k : ℕ, ∑ a, (A a : ℂ) ^ k = ∑ a, (α a : ℂ) ^ (f * k)) ∧ ∀ a, ‖(A a : ℂ)‖ ≤ Real.sqrt q' := by
  refine ⟨fun k => ?_, fun a => ?_⟩
  · have := congrArg (fun m : Multiset ℂˣ => (m.map fun z : ℂˣ => (z : ℂ) ^ k).sum) h
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum, Units.val_pow_eq_pow_val, ← pow_mul] at this
    exact this
  · have hm : A a ∈ Finset.univ.val.map fun a => α a ^ f := h ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
    obtain ⟨b, -, e⟩ := Multiset.mem_map.1 hm
    rw [← e, hq, Units.val_pow_eq_pow_val, norm_pow, Nat.cast_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) (hα b) f).trans (Real.le_sqrt_of_sq_le (le_of_eq ?_))
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end Pb2

open Pb2


end UpperTheory.ConvolutionTheory.R
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.R

namespace Cc2

theorem norm_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  rw [show normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) from Nat.card_eq_fintype_card]
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero (𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, Finset.card_univ]
    exact not_le.1 hlt

theorem int_le {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] (A : ValuationSubring Ω) (x : 𝓞 M) :
    A.valuation (algebraMap M Ω x) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap M Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

theorem moved {K M : Type} [Field K] [Field M] [NumberField M] [Algebra K M] (τ : M ≃ₐ[K] M) (h : τ ≠ 1) :
    ∃ θ : 𝓞 M, τ θ ≠ θ := by
  by_contra hn
  push Not at hn
  refine h (AlgEquiv.ext fun x => ?_)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  rw [map_div₀]
  exact congrArg₂ (· / ·) (hn a) (hn b)

end Cc2

open Cc2

theorem classChar2 : ClassChar := by
  intro K M _ _ _ _ _ _ _ _ hl
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fact.mk hl
  haveI : NeZero (Module.finrank K M) := ⟨hl.ne_zero⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  let Ω := AlgebraicClosure M
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  let r : G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hr : ∀ s (x : M), algebraMap M Ω (r s x) = s (algebraMap M Ω x) := fun s x => AlgEquiv.restrictNormal_commutes s M x
  let e : (M ≃ₐ[K] M) ≃* rootsOfUnity (Module.finrank K M) (Qbar 2) :=
    mulEquivOfPrimeCardEq (IsGalois.card_aut_eq_finrank K M) (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ _)
  let δ : G K Ω →* (Qbar 2)ˣ := ((rootsOfUnity _ _).subtype.comp e.toMonoidHom).comp r
  have hδ : ∀ s, δ s = 1 ↔ r s = 1 := fun s =>
    ⟨fun h => e.injective (Subtype.ext (h.trans (by rw [map_one]; rfl))), fun h => by simp [δ, h]⟩
  choose θ hθ using fun τ : {τ : M ≃ₐ[K] M // τ ≠ 1} => moved τ.1 τ.2
  have hc : Continuous δ := by
    refine continuous_of_isOpen_ker' δ (Subgroup.isOpen_mono
      (H₁ := ⨅ τ, MulAction.stabilizer (G K Ω) (algebraMap M Ω (θ τ))) (fun s hs => (hδ s).2 ?_) ?_)
    · by_contra h
      exact hθ ⟨r s, h⟩ ((algebraMap M Ω).injective ((hr s _).trans (Subgroup.mem_iInf.1 hs ⟨r s, h⟩)))
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun τ => stabilizer_isOpen_of_isIntegral _
  obtain ⟨η, ⟨ho, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι δ hc hl.pos (MonoidHom.ext fun s => (e (r s)).2)
  have hv1 : ∀ v, η.val v ^ Module.finrank K M = 1 := fun v => by
    rw [← Pb2.val_pow, show η ^ Module.finrank K M = 1 from ho]; rfl
  have ev : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      ∀ τ : {τ : M ≃ₐ[K] M // τ ≠ 1}, RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ ∉ w.asIdeal :=
    Filter.eventually_all.2 fun τ => by
      have h0 : Ideal.span {RingOfIntegers.mapRingEquiv τ.1.toRingEquiv (θ τ) - θ τ} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_eq_zero]
        exact fun h => hθ τ (congrArg (fun x : 𝓞 M => (x : M)) h)
      exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (not_not.1 hv)
  have key : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, η.UnrAt (w.under (𝓞 K)) ∧
      (η.val (w.under (𝓞 K)) = 1 ↔ normV w = normV (w.under (𝓞 K))) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ normV w = normV (w.under (𝓞 K)) ^ Module.finrank K M) := by
    filter_upwards [ev, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (decomp K M hl)] with w hw hd
    have hd' := hd.imp (fun h => h.2 w rfl) fun h => h.2 w rfl
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    have hv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hur : ∀ s ∈ Ine (F := K) A, δ s = 1 := fun s hs => (hδ s).2 (by
      by_contra h
      refine hw ⟨r s, h⟩ ((hA _).1 ?_)
      have := hs.2 _ (int_le A (θ ⟨r s, h⟩))
      rw [← hr, ← map_sub] at this
      exact this)
    obtain ⟨φ, hφ⟩ := exists_isFrob hv
    have hu := (hL.unr_iff ha (Or.inr rfl) hv).1 hur
    have h3 := hL.frob_unr ha (Or.inr rfl) hu hv hφ
    have h4 : η.val (w.under (𝓞 K)) = 1 ↔ δ φ = 1 := by
      rw [← Units.val_eq_one, ← Units.val_eq_one (a := δ φ), h3, inv_eq_one, map_eq_one_iff _ ι.symm.injective]
    have hq : 1 < normV (w.under (𝓞 K)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
    refine ⟨hu, h4.trans ⟨fun h => ?_, fun h => ?_⟩, hd'⟩
    · refine hd'.resolve_right fun h' => ?_
      have hle : normV w ≤ normV (w.under (𝓞 K)) := norm_le w hq fun x => by
        have h2 := hφ.2 _ (int_le A x)
        rw [← hr, (hδ φ).1 h] at h2
        rw [← hA]
        simpa using h2
      have := Nat.pow_lt_pow_right hq hl.one_lt
      rw [pow_one, ← h'] at this
      omega
    · obtain ⟨ψ, hψ⟩ := exists_isFrob hA
      have hψ' : IsFrob (F := K) A (normV (w.under (𝓞 K))) (res K Ω M ψ) := by
        rw [← h]
        exact ⟨hψ.1, hψ.2⟩
      have h1 := hur _ (inv_mul_mem_Ine_of_isFrob hφ hψ')
      have h2 : δ (res K Ω M ψ) = 1 := (hδ _).2 (AlgEquiv.ext fun x => (algebraMap M Ω).injective ((hr _ x).trans (ψ.commutes x)))
      rwa [map_mul, h2, mul_one, map_inv, inv_eq_one] at h1
  refine ⟨η, ⟨?_, ho, ?_⟩, key.mono fun w hw => ⟨hw.1, ?_⟩⟩
  · rintro rfl
    haveI : Nontrivial (M ≃ₐ[K] M) := Finite.one_lt_card_iff_nontrivial.1 (IsGalois.card_aut_eq_finrank K M ▸ hl.one_lt)
    obtain ⟨τ, hτ⟩ := exists_ne (1 : M ≃ₐ[K] M)
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
    refine hτ ((hδ s).1 (Units.ext ?_))
    obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω s)
    rw [hL x s hx, infPow_zero, lPow_zero]
    simp
  · filter_upwards [key] with w hw f hf
    rcases hw.2.2 with h | h
    · rw [hw.2.1.2 h, one_pow]
    · rw [show f = Module.finrank K M from
        Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm _) (hf.symm.trans h), hv1]
  · by_cases h : η.val (w.under (𝓞 K)) = 1
    · exact Or.inl (hw.2.1.1 h)
    · refine Or.inr ?_
      rw [← orderOf_eq_prime (hv1 _) h]
      exact IsPrimitiveRoot.orderOf _

end UpperTheory.ConvolutionTheory.R
end
end

section
open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS in
theorem UpperTheory.ConvolutionTheory.R.sysEx :
    SysEx := by
  intro E _ _ _ X hfin hX
  classical
  have hRSU : RSU := rankin_selberg_unitary_of_pole norm_exponent_equality satake_twist_holds PositivityTheory.AdelicQuotientData.rsPole
  have hBd : GlobalTheory.Published.JacquetShalikaBound := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
  have hDO : DetOne := determinant_one_condition_holds
  have hPO : PrimeOff := prime_sum_converges_and_diverges
  have : Fintype X := hfin.fintype
  choose S0 hS0 using fun x y : X =>
    hRSU E x.1.1 y.1.1 x.1.2 y.1.2 (hX x x.2).1 (hX y y.2).1 (hX x x.2).2.1 (hX y y.2).2.1
  have hw : ∀ᶠ w in Filter.cofinite, ∀ x : X, ∃ B, x.1.2.HasSat w B :=
    Filter.eventually_all.2 fun x => (hX x x.2).2.2
  refine ⟨(Filter.eventually_cofinite.1 hw).toFinset ∪ Finset.univ.biUnion (fun p : X × X => S0 p.1 p.2), fun S hS => ?_⟩
  have hex : ∀ (x : X) (w : Off E S), ∃ f : Fin x.1.1 → ℂˣ, x.1.2.HasSat w.1 (Finset.univ.val.map f) := by
    intro x w
    have h : ∀ x : X, ∃ B, x.1.2.HasSat w.1 B := by
      by_contra h
      exact w.2 (hS (Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact h)))
    obtain ⟨B, hB⟩ := h x
    obtain ⟨f, hf⟩ := RigidityLemmas.exists_fin _ hB.card
    exact ⟨f, hf ▸ hB⟩
  choose α hα using hex
  have hsub : ∀ x y : X, S0 x y ⊆ S := fun x y z hz =>
    hS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(x, y), Finset.mem_univ _, hz⟩))
  refine ⟨α, hα, hPO E S, fun x => (hX x x.2).1, fun x w a => ?_, fun x w => ?_, fun x y => ?_⟩
  · have h := (hBd E x.1.1 x.1.2 (hX x x.2).2.1 w.1 _ (hα x w) (α x w a)
      (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
    show ‖((α x w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
    rw [Real.sqrt_eq_rpow]
    exact h.le
  · have h := hDO E x.1.1 x.1.2 w.1 _ (hX x x.2).2.1 (hα x w)
    rw [← Finset.prod_eq_multiset_prod, Units.coe_prod] at h
    exact h
  · obtain ⟨F, σ₀, hF, hFe⟩ := hS0 x y S (hsub x y) (α x) (α y) (hα x) (hα y)
    refine ⟨F, σ₀, hF, fun σ hσ => ?_⟩
    rw [hFe σ hσ]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg (fun h => hxy (Subtype.ext (by simpa using h))), if_neg hxy]
      rfl
end

section
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

private theorem normV_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem one_lt_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  rw [normV_eq]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem UpperTheory.ConvolutionTheory.R.coverEx :
    Decomp → CoverEx := by
  classical
  intro hD K M _ _ _ _ _ _ _ _ hl η hη S₀ T₀
  have hD' := hD K M hl
  obtain ⟨⟨-, -, hN⟩, hG⟩ := hη
  have hNG := hN.and hG
  beta_reduce at hD'
  rw [Filter.eventually_cofinite] at hD' hNG
  have hten : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite :=
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M
  set S : Finset (HeightOneSpectrum (𝓞 K)) :=
    S₀ ∪ hD'.toFinset ∪ (T₀ ∪ hNG.toFinset).image (fun w => w.under (𝓞 K)) with hS
  have hTfin : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
    have := hten.eventually S.eventually_cofinite_notMem
    rw [Filter.eventually_cofinite] at this
    simpa using this
  set T := hTfin.toFinset with hT
  have hmemT : ∀ w, w ∈ T ↔ w.under (𝓞 K) ∈ S := fun w => by simp [hT]
  have hgood : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1) ∧ η.UnrAt (w.under (𝓞 K)) ∧
      (normV w = normV (w.under (𝓞 K)) ∨ IsPrimitiveRoot (η.val (w.under (𝓞 K))) (Module.finrank K M)) := by
    intro w hw
    by_contra h
    exact hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_union_right _ (hNG.mem_toFinset.2 h))))
  have hdec : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = Module.finrank K M ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v) ∨
      (Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → normV w = normV v ^ Module.finrank K M) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hD'.mem_toFinset.2 h)))
  have hex : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v := by
    intro v hv
    have : Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v} ≠ 0 := by
      rcases hdec v hv with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), normV v ^ Module.finrank K M ≠ normV v := by
    intro v
    have := Nat.pow_lt_pow_right (one_lt_normV v) hl.one_lt
    rw [pow_one] at this
    exact this.ne'
  let u : Off M T → Off K S := fun w => ⟨w.1.under (𝓞 K), fun h => w.2 ((hmemT _).2 h)⟩
  let f : Off M T → ℕ := fun w => if normV w.1 = normV (w.1.under (𝓞 K)) then 1 else Module.finrank K M
  have hnorm : ∀ w, normV w.1 = normV (u w).1 ^ f w := by
    intro w
    by_cases h : normV w.1 = normV (w.1.under (𝓞 K))
    · simp only [f, if_pos h, pow_one]; exact h
    · simp only [f, if_neg h]
      rcases hdec _ (u w).2 with h' | h'
      · exact absurd (h'.2 _ rfl) h
      · exact h'.2 _ rfl
  have hcard : ∀ v : Off K S, Nat.card {w // u w = v} =
      Nat.card {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 K) = v.1} := by
    intro v
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, congrArg Subtype.val w.2⟩
        invFun := fun w => ⟨⟨w.1, fun h => v.2 (w.2 ▸ (hmemT _).1 h)⟩, Subtype.ext w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨S, T, u, f, fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv), fun w hw => (hmemT w).2
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_union_left _ hw))), fun _ => rfl, ?_, hnorm, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw⟩ := hex v.1 v.2
    exact hw ▸ (hgood w (hw ▸ v.2)).2.1
  · intro w
    simpa only [nq, normV_eq] using hnorm w
  · intro v
    obtain ⟨w₀, hw₀⟩ := hex v.1 v.2
    have hg := hgood w₀ (hw₀ ▸ v.2)
    rw [hw₀] at hg
    rcases hdec v.1 v.2 with h | h
    · refine Or.inl ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        exact if_pos (hw' ▸ h.2 _ hw')
      · have := hg.1 1 (by rw [pow_one]; exact h.2 _ hw₀)
        rw [pow_one] at this
        simp [this]
    · refine Or.inr ⟨(hcard v).trans h.1, fun w hw => ?_, ?_⟩
      · have hw' : w.1.under (𝓞 K) = v.1 := congrArg Subtype.val hw
        refine if_neg ?_
        rw [h.2 _ hw', hw']
        exact hne _
      · rcases hg.2.2 with h' | h'
        · exact absurd ((h.2 _ hw₀).symm.trans h') (hne _)
        · exact IsPrimitiveRoot.coe_units_iff.2 h'
end

section
open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

section

variable {E : Type} [Field E] [NumberField E]

private theorem val_pow' (χ : HChar E) (j : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (χ ^ j).val w = χ.val w ^ j :=
  MonoidHom.pow_apply χ.1 j _

private theorem unr_pow {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) (j : ℕ) : (χ ^ j).UnrAt w := by
  intro x hx
  have e : (χ ^ j).loc w x = χ.loc w x ^ j := MonoidHom.pow_apply χ.1 j _
  rw [e, h x hx, one_pow]

private theorem unr_inv {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  intro x hx
  have e : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
  rw [e, h x hx, inv_one]

private theorem unit_of_pow {χ : HChar E} {l : ℕ} (hl : l ≠ 0) (h : χ ^ l = 1) : χ.IsUnitary := by
  intro x
  have e : χ.1 x ^ l = 1 := by
    have e1 : (χ ^ l).1 x = χ.1 x ^ l := MonoidHom.pow_apply χ.1 l _
    rw [← e1, h]; rfl
  have e2 : ((χ.1 x : ℂˣ) : ℂ) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e2 hl

variable [IsTotallyComplex E]

private theorem unit_twist {n : ℕ} {π : CG E n} (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) :
    (π.twist χ).IsUnitary := by
  obtain ⟨ω, hω, hc⟩ := h
  refine ⟨_, fun x => ?_, hc.twist χ⟩
  have e : (ω * χ ^ n).1 x = ω.1 x * χ.1 x ^ n := congrArg (ω.1 x * ·) (MonoidHom.pow_apply χ.1 n _)
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hω x, hχ x, one_pow, one_mul]

private theorem sat_untw {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    (h : ∃ B, (π.twist χ).HasSat w B) : ∃ B, π.HasSat w B := by
  obtain ⟨B, hB⟩ := h
  have := satake_twist_holds E n _ χ⁻¹ w B (unr_inv hχ) hB
  rw [← CG.twist_mul, mul_inv_cancel, CG.twist_one] at this
  exact ⟨_, this⟩

private theorem sat_key {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {α : Fin n → ℂˣ} (hα : π.HasSat w (Finset.univ.val.map α)) {B : Multiset ℂˣ} (hB : (π.twist χ).HasSat w B) :
    B.map (fun u : ℂˣ => (u : ℂ)) = Finset.univ.val.map fun a => (α a : ℂ) * (χ.val w : ℂ) := by
  rw [hB.unique (satake_twist_holds E n π χ w _ hχ hα), Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ => by simp

end

private theorem ev_sat {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (HeightOneSpectrum (𝓞 M))} {u : Off M T → Off K S}
    {f : Off M T → ℕ} (hu : ∀ w, (u w).1 = w.1.under (𝓞 K)) (hf : ∀ w, normV w.1 = normV (u w).1 ^ f w)
    (hs : Function.Surjective u) {sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop}
    {satE : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop} (h : WeakBC sat satE) :
    (∀ᶠ v in Filter.cofinite, ∃ B, sat v B) ∧ ∀ᶠ w in Filter.cofinite, ∃ B, satE w B := by
  constructor
  · have h' := Filter.eventually_cofinite.1 h
    have h2 := (h'.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)).eventually_cofinite_notMem
    filter_upwards [h2, S.eventually_cofinite_notMem] with v hv hvS
    obtain ⟨w, hw⟩ := hs ⟨v, hvS⟩
    have e : w.1.under (𝓞 K) = v := (hu w).symm.trans (congrArg Subtype.val hw)
    by_contra hc
    refine hv ⟨w.1, fun hg => hc ?_, e⟩
    obtain ⟨B, hB, -⟩ := hg (f w) (by rw [← hu w]; exact hf w)
    exact ⟨B, e ▸ hB⟩
  · filter_upwards [h, T.eventually_cofinite_notMem] with w hw hwT
    obtain ⟨B, -, hB⟩ := hw (f ⟨w, hwT⟩) (by have := hf ⟨w, hwT⟩; rwa [hu] at this)
    exact ⟨_, hB⟩

private theorem lift_eq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsTotallyComplex K] [IsTotallyComplex M] {n : ℕ} {π : CG K n} {ν : HChar K} {t : ℝ} (hν : ν.IsAbsPow t)
    {ι : Type} [Fintype ι] {m : ι → ℕ} {P : ∀ i, CG M (m i)} {ν' : ι → HChar M} {s : ι → ℝ}
    (hν' : ∀ i, (ν' i).IsAbsPow (s i)) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} {f : ℕ}
    {α : Fin n → ℂˣ} (hα : π.HasSat v (Finset.univ.val.map α)) {β : ∀ i, Fin (m i) → ℂˣ}
    (hβ : ∀ i, (P i).HasSat w (Finset.univ.val.map (β i)))
    (h : ∃ B, (π.twist ν).HasSat v B ∧ sumSat (fun i => (P i).twist (ν' i)) w (B.map (· ^ f))) :
    ∑ i, Finset.univ.val.map (fun a => (β i a : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s i : ℂ))) =
      Finset.univ.val.map fun a => ((α a : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(t : ℂ))) ^ f := by
  obtain ⟨B, hB, B', hB', e⟩ := h
  have e1 := sat_key (hν.1 v) hα hB
  have e2 := fun i => sat_key ((hν' i).1 w) (hβ i) (hB' i)
  simp only [(hν' _).2.1 w] at e2
  rw [hν.2.1 v] at e1
  have e3 := congrArg (Multiset.map fun u : ℂˣ => (u : ℂ)) e
  have e4 : Multiset.map (fun u : ℂˣ => (u : ℂ)) (∑ i, B' i) = ∑ i, Multiset.map (fun u : ℂˣ => (u : ℂ)) (B' i) :=
    map_sum (Multiset.mapAddMonoidHom fun u : ℂˣ => (u : ℂ)) B' Finset.univ
  have e5 := congrArg (Multiset.map fun c : ℂ => c ^ f) e1
  rw [Multiset.map_map, Multiset.map_map] at e5
  rw [e4, Multiset.map_map] at e3
  simp only [e2] at e3
  rw [← e3]
  exact Eq.trans (Multiset.map_congr rfl fun a _ => by simp) e5

theorem UpperTheory.ConvolutionTheory.R.count :
    AbsCount → SysEx → CoverEx → Count := by
  intro hA hS hC K M _ _ _ _ _ _ _ _ hl η hη n π π₁ ι _ m P hn hm hπ hπ₁
  classical
  obtain ⟨ν, hν, hU⟩ := unit_exponent_holds K
  obtain ⟨ν', hν', hU'⟩ := unit_exponent_holds M
  obtain ⟨π0, t, hu0, rfl⟩ := hU n π hn
  obtain ⟨π1, t1, hu1, rfl⟩ := hU n π₁ hn
  choose P0 s huP hP using fun i => hU' (m i) (P i) (hm i)
  obtain rfl : P = fun i => (P0 i).twist (ν' (s i)) := funext hP
  have hηl : η ^ Module.finrank K M = 1 := hη.1.2.1
  have hηu : ∀ j : ℕ, (η ^ j).IsUnitary := fun j =>
    unit_of_pow hl.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hηl, one_pow])
  obtain ⟨S1, T1, u1, f1, -, -, hu1', hunr1, hf1, hc1⟩ := hC K M hl η hη ∅ ∅
  have hs1 : Function.Surjective u1 := fun v => by
    have : Nat.card {w // u1 w = v} ≠ 0 := by
      rcases hc1.fib v with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  obtain ⟨e0, eP⟩ := ev_sat hu1' hf1 hs1 hπ
  obtain ⟨e1, -⟩ := ev_sat hu1' hf1 hs1 hπ₁
  let X : Set (Σ a, CG K a) := insert ⟨n, π1⟩ (Set.range fun j : ℕ => ⟨n, π0.twist (η ^ j)⟩)
  let X' : Set (Σ a, CG M a) := Set.range fun i => ⟨m i, P0 i⟩
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (((Set.finite_lt_nat (Module.finrank K M)).image
      fun j : ℕ => (⟨n, π0.twist (η ^ j)⟩ : Σ a, CG K a)).subset ?_)
    rintro _ ⟨j, rfl⟩
    exact ⟨j % Module.finrank K M, Nat.mod_lt _ hl.pos, by
      beta_reduce; rw [← pow_eq_pow_mod j hηl]⟩
  obtain ⟨S0, hS0⟩ := hS K X hXf (by
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact ⟨hn, hu1, e1.mono fun v hv => sat_untw ((hν _).1 v) hv⟩
    · refine ⟨hn, unit_twist hu0 (hηu j), ?_⟩
      filter_upwards [e0, S1.eventually_cofinite_notMem] with v hv hvS
      obtain ⟨B, hB⟩ := sat_untw ((hν _).1 v) hv
      exact ⟨_, satake_twist_holds K n π0 _ v B (unr_pow (hunr1 ⟨v, hvS⟩) j) hB⟩)
  obtain ⟨T0, hT0⟩ := hS M X' (Set.finite_range _) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨hm i, huP i, eP.mono fun w ⟨B, B', hB', _⟩ => sat_untw ((hν' _).1 w) ⟨_, hB' i⟩⟩)
  have hbad := Filter.eventually_cofinite.1 (hπ.and hπ₁)
  obtain ⟨S, T, u, f, hS0S, hT0T, hu, hunr, hf, hc⟩ := hC K M hl η hη S0 (T0 ∪ hbad.toFinset)
  obtain ⟨α, hα, hsys⟩ := hS0 S hS0S
  obtain ⟨β, hβ, hsys'⟩ := hT0 T (Finset.subset_union_left.trans hT0T)
  have hgood : ∀ w : Off M T, (∃ B, (π0.twist (ν t)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))) ∧ ∃ B, (π1.twist (ν t1)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w)) := fun w => by
    have h1 := hf w
    rw [hu] at h1 ⊢
    have h2 : w.1 ∉ hbad.toFinset := fun h => w.2 (hT0T (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact ⟨h2.1 _ h1, h2.2 _ h1⟩
  let x : X := ⟨⟨n, π1⟩, Or.inl rfl⟩
  let y : ℕ → X := fun j => ⟨⟨n, π0.twist (η ^ j)⟩, Or.inr ⟨j, rfl⟩⟩
  let z : ι → X' × ℝ := fun i => (⟨⟨m i, P0 i⟩, i, rfl⟩, s i)
  have hy0 : ∀ v : Off K S, π0.HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := fun v => by
    have : (π0.twist (η ^ 0)).HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := hα (y 0) v
    rwa [pow_zero, CG.twist_one] at this
  obtain ⟨ht, hs, hcount⟩ := hA _ _ _ nq nq u f _ hl.pos hc X X' _ _ _ _ hsys hsys' ι x y z t1 t
    (fun j v => by
      have := sat_key (unr_pow (hunr v) j) (hy0 v) (hα (y j) v)
      rw [Multiset.map_map, val_pow', Units.val_pow_eq_pow_val] at this
      rw [Multiset.map_map]
      exact this)
    (fun w => lift_eq (hν t1) (fun i => hν' (s i)) (hα x (u w)) (fun i => hβ (z i).1 w) (hgood w).2)
    (fun w => lift_eq (hν t) (fun i => hν' (s i)) (hy0 (u w)) (fun i => hβ (z i).1 w) (hgood w).1)
  subst ht
  have hs' : ∀ i, s i = t1 := hs
  have key : ∀ {a b : ℕ} (σ : CG M a) (σ' : CG M b) (χ : HChar M),
      (⟨a, σ.twist χ⟩ : Σ a, CG M a) = ⟨b, σ'.twist χ⟩ ↔ (⟨a, σ⟩ : Σ a, CG M a) = ⟨b, σ'⟩ := by
    intro a b σ σ' χ
    constructor
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      exact congrArg _ (CG.twist_injective χ (eq_of_heq (Sigma.mk.inj e).2))
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      rw [eq_of_heq (Sigma.mk.inj e).2]
  refine Eq.trans (congrArg Finset.card (Finset.ext fun j => ?_))
    (hcount.trans (congrArg Finset.card (Finset.ext fun p => ?_)))
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [← CG.twist_mul, mul_comm, CG.twist_mul, Subtype.ext_iff]
    constructor
    · intro e
      exact congrArg (Sigma.mk n) (CG.twist_injective _ e)
    · intro e
      rw [eq_of_heq (Sigma.mk.inj e).2]
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [Subtype.ext_iff, hs' p.1, hs' p.2, key]
end

section
open UpperTheory.ConvolutionTheory.R

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V.Published

theorem UpperTheory.ConvolutionTheory.R.normCharPow :
    Count → NormCharPow := by
  classical
  intro hN K M _ _ _ _ _ _ _ _ hl η hη
  have hp : ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 K)), (η ^ n).val v = η.val v ^ n :=
    fun n v => MonoidHom.pow_apply η.1 n _
  refine ⟨fun χ hχ => ?_, fun j hj0 hjl => ⟨fun h => ?_, ?_, ?_⟩⟩
  · have hW : ∀ ψ : HChar K, (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ,
        Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) ^ f → ψ.val (w.under (𝓞 K)) ^ f = 1) →
        WeakBC (CG.ofChar ψ).HasSat (sumSat (m := fun _ : Unit => 1) fun _ => CG.ofChar (1 : HChar M)) := by
      intro ψ h
      rw [sumSat_unit]
      filter_upwards [h, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually
        (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ))] with w h1 h2 f hf
      refine ⟨_, CG.hasSat_ofChar h2, ?_⟩
      rw [Multiset.map_singleton, h1 f hf]
      exact CG.hasSat_ofChar (χ := 1) (w := w) fun _ _ => rfl
    have h1 := hN K M hl η hη 1 (CG.ofChar 1) (CG.ofChar χ) Unit (fun _ => 1) (fun _ => CG.ofChar 1) le_rfl
      (fun _ => le_rfl) (hW 1 (Filter.Eventually.of_forall fun w f _ => one_pow f)) (hW χ hχ.2.2)
    have h2 : 0 < ((Finset.range (Module.finrank K M)).filter
        fun j => CG.ofChar χ = (CG.ofChar 1).twist (η ^ j)).card := by
      rw [h1]
      exact Finset.card_pos.2 ⟨((), ()), by simp⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h2
    rw [Finset.mem_filter, Finset.mem_range, CG.twist_ofChar, one_mul] at hj
    have e := CG.ofChar_injective hj.2
    refine ⟨j, Nat.pos_of_ne_zero ?_, hj.1, e⟩
    rintro rfl
    exact hχ.1 (e.trans (pow_zero _))
  · haveI := Fact.mk hl
    have ho := orderOf_eq_prime hη.1.2.1 hη.1.1
    have := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one h)
    omega
  · rw [← pow_mul, mul_comm, pow_mul, hη.1.2.1, one_pow]
  · refine hη.1.2.2.mono fun w hw f hf => ?_
    rw [hp, ← pow_mul, mul_comm, pow_mul, hw f hf, one_pow]
end

section
open UpperTheory.ConvolutionTheory.R

open GlobalTheory.CuspRep Formalism.L2.Host

theorem UpperTheory.ConvolutionTheory.R.fibreCG :
    ClassChar → Count → NormCharPow → FibreCG := by
  intro hC hN hP K M _ _ _ _ _ _ _ _ hl n π P hn hπ
  classical
  obtain ⟨η, hη⟩ := hC K M hl
  obtain ⟨hp1, hp2⟩ := hP K M hl η hη
  have key : ∀ π₁ : CG K n, UpperTheory.V.Published.WeakBC π₁.HasSat P.HasSat →
      ((Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j)).card = 1 := by
    intro π₁ h₁
    have := hN K M hl η hη n π π₁ Unit (fun _ => n) (fun _ => P) hn (fun _ => hn)
      (by rw [sumSat_unit]; exact hπ) (by rw [sumSat_unit]; exact h₁)
    convert this using 1
    simp
  refine ⟨fun χ hχ he => ?_, fun π₁ h₁ => ?_⟩
  · obtain ⟨j, hj0, hjl, rfl⟩ := hp1 χ hχ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π hπ)
    have h0 : 0 ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range, pow_zero, CG.twist_one]
      exact ⟨hl.pos, rfl⟩
    have h1 : j ∈ (Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjl, he.symm⟩
    rw [ha, Finset.mem_singleton] at h0 h1
    omega
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (key π₁ h₁)
    have h1 : a ∈ (Finset.range (Module.finrank K M)).filter fun j => π₁ = π.twist (η ^ j) := by
      rw [ha]; exact Finset.mem_singleton_self a
    rw [Finset.mem_filter, Finset.mem_range] at h1
    refine ⟨η ^ a, ?_, h1.2.symm⟩
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact Or.inl (pow_zero _)
    · exact Or.inr (hp2 a h h1.1)
end

section
open UpperTheory.ConvolutionTheory.R

open NumberField in
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.R.fibre :
    FibreCG → Fibre := by
  intro H K M _ _ _ _ _ _ hK hM hp n hn π P hbc
  rcases π with @⟨_, π⟩ | @⟨hR, π⟩
  swap
  · exact (not_both K hR hK).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR hM).elim
  obtain ⟨h1, h2⟩ := H K M hp n (GlobalTheory.CuspRep.CG.mk π) (GlobalTheory.CuspRep.CG.mk P) hn hbc
  refine ⟨fun η hη hi => h1 η hη (Quotient.sound hi), fun π₁ hbc₁ => ?_⟩
  rcases π₁ with @⟨_, π₁⟩ | @⟨hR, π₁⟩
  swap
  · exact (not_both K hR hK).elim
  obtain ⟨η, hη, e⟩ := h2 (GlobalTheory.CuspRep.CG.mk π₁) hbc₁
  exact ⟨η, hη, Quotient.exact e⟩
end

section
open UpperTheory.ConvolutionTheory.R

theorem UpperTheory.ConvolutionTheory.R.twoParts :
    ClassChar → Count → NormCharPow → TwoParts := by
  classical
  intro hC hCount hN K M _ _ _ _ _ _ _ _ hp n π ι _ m P hn hm hι hW
  obtain ⟨η, hη⟩ := hC K M hp
  have h1 := hCount K M hp η hη n π π ι m P hn hm hW hW
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card ι from hι)
  have h2 : 1 < ((Finset.range (Module.finrank K M)).filter fun j => π = π.twist (η ^ j)).card := by
    rw [h1, Finset.one_lt_card]
    refine ⟨(a, a), by simp, (b, b), by simp, fun h => hab (congrArg Prod.fst h)⟩
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_ne h2 0
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨η ^ j, (hN K M hp η hη).2 j (Nat.pos_of_ne_zero hj0) hj.1, hj.2.symm⟩
end

section
open PositivityTheory.Rg.Tf.ChR

namespace UpperTheory.ConvolutionTheory.R

theorem count_holds : Count := count (absCount2 bcSum_holds zeroExp logAsym) sysEx (coverEx decomp)

theorem normCharPow_holds : NormCharPow := normCharPow count_holds

theorem fibreCG_holds : FibreCG := fibreCG classChar2 count_holds normCharPow_holds

theorem fibre_holds : Fibre := fibre fibreCG_holds

theorem twoParts_holds : TwoParts := twoParts classChar2 count_holds normCharPow_holds

theorem partA_holds : PartA := by
  intro E _ _ _ n P ι _ m Ps hn hm hι h
  obtain ⟨s, -⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity E Unit ι (fun _ => n) m (fun _ => P) Ps (fun _ => hn) hm
    (h.mono fun w ⟨C, B, h1, h2, h3⟩ => ⟨fun _ => C, B, fun _ => h1, h2, by simp [h3]⟩)
  have := Fintype.card_congr s
  simp at this
  omega

end UpperTheory.ConvolutionTheory.R
end
