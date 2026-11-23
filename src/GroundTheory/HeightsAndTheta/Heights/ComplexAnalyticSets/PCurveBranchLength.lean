module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem localMult_ker_eval_eq_zero {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dite_eq_left (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl

theorem CurveBranchLength.proof (hN : CurveNormalisationLength.Statement)
    (hB : BranchNormalisation.Statement) : CurveBranchLength.Statement := by
  intro n I u q m c ord hrad hcov hdisj hord
  have hlin : ∀ x, eval x (linForm u) = linEval u x := fun x ↦ by simp [linForm, linEval]
  have hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b := by
    intro b
    obtain ⟨H, -, hH, hF⟩ := hord b
    have h0 := hF 0 (Metric.mem_ball_self (c b).radius_pos)
    simp only [(c b).map_zero] at h0
    rw [h0]
    simp [hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]
  by_cases hmain : linEval u q = 0 ∧ 0 < m
  swap
  · have hsum : ∑ b, ord b = 0 := Finset.sum_eq_zero fun b _ ↦ by
      by_contra hb
      exact hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩
    rw [hsum]
    by_cases hu : linEval u q = 0
    · have hm : m = 0 := by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩
      subst hm
      obtain ⟨N, hNq, hsub⟩ := hcov
      have hq : q ∉ zeroSet I := fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩
      obtain ⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by
        by_contra h
        push Not at h
        exact hq h
      exact localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq
    · exact localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])
  obtain ⟨hu0, hm⟩ := hmain
  have hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q := by
    rintro b _ ⟨t, ht, rfl⟩ hx
    obtain ⟨H, -, hH, hF⟩ := hord b
    rw [show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero] at hx
    have ht0 : t 0 = 0 := hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)
    have ht' : t = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0
    rw [ht', (c b).map_zero]
  obtain ⟨hdim, hnzd, e, he⟩ := hB n I q m c hrad hm hcov
    fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)
  have hordb : ∀ b, branchOrder (c b) (linForm u) = ord b := fun b ↦
    branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)
  have hL := hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype] at hL
  simp only [(he _).1, mul_one, (he _).2, hordb] at hL
  exact_mod_cast hL

end GroundTheory.Heights₂.Heights
