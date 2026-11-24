module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeRpowNegLevelLe
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SummableAndTsumLeTwoMulDivOfLeDivPow
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.DfcHigh
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum
public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NinthBoundArithB, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts, Formalism.SharpRestriction.GrowthBounds.LogarithmicSums

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def FamilyAskBounds {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RequiresAll (X x i)

def RemainingCountingStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

def FamilyFourthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K

def RestW {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightVectorExists (Fm.D x i) (Fm.L x i) (X x i) K

def FamilyFifthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) → PointsLemma (Fm.D x i) (Fm.L x i) (X x i) K

def RestT {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem stmtEF_of {eps : ℝ} (Fm : FamP eps) (h0 : FamilyAskBounds Fm) (h1 : RemainingCountingStatement Fm) (h2 : FamilyFourthBound Fm) (hW : RestW Fm)
    (h3 : FamilyFifthBound Fm) (hT : RestT Fm) : FamilyClosedForm Fm := by
  intro K hK C31 Ce Cm hC31 hCe hCm
  obtain ⟨C, hC, hG⟩ := h1 K hK C31 Ce Cm hC31 hCe hCm
  refine ⟨C, hC, fun X Y hA => ?_⟩
  obtain ⟨a0, ha0⟩ := h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a1, ha1⟩ := hG X Y hA
  obtain ⟨a2, ha2⟩ := h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨aW, haW⟩ := hW K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a3, ha3⟩ := h3 K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  obtain ⟨aT, haT⟩ := hT K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  refine ⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 (max a2 (max aW (max a3 aT)))), fun x hx i => ?_⟩
  · exact tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))
  · simp only [ge_iff_le, max_le_iff] at hx
    obtain ⟨e0, e1, e2, eW, e3, eT⟩ := hx
    have g0 := ha0 x e0 i
    have g1 := ha1 x e1 i
    have g2 := ha2 x e2 i
    have gW := haW x eW i
    have g3 := ha3 x e3 i g1
    have gT := haT x eT i
    have g1' := g1 (aL (Fm.L x i)) (bL (Fm.L x i))
    refine ⟨g1' ?_, g2, g3, gW, fun a b ha hb p hp _ => g0 a b ha hb p hp, gT⟩

    intro t ht
    unfold aL bL
    simp only [dif_pos ht]
    exact ⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩

theorem stmtF_of_stmtEF {eps : ℝ} (Fm : FamP eps) (h : FamilyClosedForm Fm) : KudlaFamilyStatement Fm := by
  intro K hK X Y hA
  obtain ⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩ := hA
  obtain ⟨C, hC, hP⟩ := h K hK C31 Ce Cm hC31 hCe hCm
  exact ⟨C, hP X Y hA'⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.As

variable {D : D7} {L : SizeData₂ D}

theorem shift_ge (p y κ : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y)
    (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  refine Summable.tsum_le_tsum (fun e => ?_) (hs _ fun e => by linarith [hw e]) (hs _ hw)
  split_ifs
  · exact max_le_max le_rfl (by linarith)
  · exact le_rfl

theorem shift_le (p y κ A : ℝ) (hp : 2 ≤ p) (hκ : 0 ≤ κ) (hy0 : 0 ≤ y) (hyA : y ≤ A) (hA : 1 ≤ A)
    (w : ℕ → ℝ) (hw : ∀ e, 1 ≤ w e) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A := by
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : 1 / p < 1 := by rw [div_lt_one hp0]; linarith
  have hg : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left y
  have hs : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
      Summable (fun e => if Q e then max 0 (y / p ^ e - c e) else 0) := by
    intro c hc
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hg
    · split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    · have hpe : y / p ^ e = y * (1 / p) ^ e := by rw [one_div_pow, div_eq_mul_one_div]
      split_ifs
      · exact max_le (mul_nonneg hy0 (by positivity)) (by rw [← hpe]; linarith [hc e])
      · exact mul_nonneg hy0 (by positivity)
  have hL0 : 0 ≤ Real.logb p A := Real.logb_nonneg hp1 hA
  set n := ⌊Real.logb p A⌋₊ with hn
  set ind : ℕ → ℝ := fun e => if Q e ∧ (p : ℝ) ^ e < A then 1 else 0 with hind
  have hlog : ∀ e : ℕ, (p : ℝ) ^ e < A → e ≤ n := by
    intro e he
    apply Nat.le_floor
    have h1 : Real.logb p ((p : ℝ) ^ e) = e := by
      rw [Real.logb_pow, Real.logb_self_eq_one hp1, mul_one]
    rw [← h1]
    exact (Real.logb_lt_logb hp1 (by positivity) he).le
  have hsupp : ∀ e ∉ Finset.range (n + 1), ind e = 0 := by
    intro e he
    simp only [hind]
    rw [if_neg]
    rintro ⟨_, h⟩
    exact he (Finset.mem_range.2 (Nat.lt_succ_of_le (hlog e h)))
  have hind_sum : Summable ind := summable_of_ne_finset_zero hsupp
  have hcount : ∑' e, ind e ≤ Real.logb p A := by
    rw [tsum_eq_sum hsupp]
    have hsub : ∑ e ∈ Finset.range (n + 1), ind e ≤
        (((Finset.range (n + 1)).filter Odd).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      simp only [hind]
      split_ifs with h1 h2 <;> first | exact absurd (hQ e h1.1) h2 | norm_num
    have hodd : ((Finset.range (n + 1)).filter Odd).card ≤ n := by
      have h := Finset.card_le_card_of_injOn (fun e => e / 2) (s := (Finset.range (n + 1)).filter Odd) (t := Finset.range ((n + 1) / 2))
        (by
          intro e he
          have he' : e ≤ n ∧ Odd e := by simpa using he
          obtain ⟨h1, k, rfl⟩ := he'
          simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
          omega)
        (by
          intro e1 he1 e2 he2 heq
          have he1' : e1 ≤ n ∧ Odd e1 := by simpa using he1
          have he2' : e2 ≤ n ∧ Odd e2 := by simpa using he2
          obtain ⟨_, k1, rfl⟩ := he1'
          obtain ⟨_, k2, rfl⟩ := he2'
          simp only at heq
          omega)
      rw [Finset.card_range] at h
      omega
    calc ∑ e ∈ Finset.range (n + 1), ind e ≤ (((Finset.range (n + 1)).filter Odd).card : ℝ) := hsub
      _ ≤ (n : ℝ) := by exact_mod_cast hodd
      _ ≤ Real.logb p A := Nat.floor_le hL0
  have hterm : ∀ e, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e := by
    intro e
    simp only [hind]
    by_cases hq : Q e
    · by_cases hu : 0 < y / p ^ e - w e
      · have hpA : (p : ℝ) ^ e < A := by
          have h1 : 1 < y / p ^ e := lt_of_le_of_lt (hw e) (by linarith)
          rw [lt_div_iff₀ (by positivity)] at h1
          linarith
        rw [if_pos hq, if_pos hq, if_pos ⟨hq, hpA⟩, max_eq_right hu.le]
        have := le_max_right 0 (y / p ^ e - (w e + κ))
        linarith
      · rw [if_pos hq, if_pos hq, max_eq_left (not_lt.1 hu)]
        have h1 := le_max_left 0 (y / p ^ e - (w e + κ))
        have h2 : 0 ≤ κ * (if Q e ∧ (p : ℝ) ^ e < A then (1 : ℝ) else 0) :=
          mul_nonneg hκ (by split_ifs <;> norm_num)
        linarith
    · rw [if_neg hq, if_neg hq, if_neg (fun h => hq h.1)]
      simp
  have hsκ := hs (fun e => w e + κ) (fun e => by linarith [hw e])
  calc ∑' e, (if Q e then max 0 (y / p ^ e - w e) else 0)
      ≤ ∑' e, ((if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ind e) :=
        Summable.tsum_le_tsum hterm (hs _ fun e => by linarith [hw e]) (hsκ.add (hind_sum.mul_left κ))
    _ = ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * ∑' e, ind e := by
        rw [Summable.tsum_add hsκ (hind_sum.mul_left κ), tsum_mul_left]
    _ ≤ ∑' e, (if Q e then max 0 (y / p ^ e - (w e + κ)) else 0) + κ * Real.logb p A :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcount hκ)

theorem n_pos (D : D7) : 1 ≤ D.R.n := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  unfold Formalism.BasicNotions.Ranks.n
  omega

theorem fill_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ)) (j : ℕ)
    (z : Bool × HH D) : L.sc.w'' D.R.n ≤ fill X b j z := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast n_pos D
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    show L.sc.b' / (L.sc.x * D.R.n) ≤ L.sc.b' / L.sc.x
    exact div_le_div_of_nonneg_left hb'0 (by linarith) (by nlinarith)
  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    calc L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := hw1
      _ = L.sc.b / L.sc.X' := by
        show L.sc.x * L.sc.b / L.sc.X' / L.sc.x = L.sc.b / L.sc.X'
        field_simp
      _ ≤ L.sc.b := div_le_self (by linarith) hX1
  unfold fill
  by_cases htop : IsTopPl D z
  · rw [if_pos (show z.1 = false ∧ z.2 ∈ D.host.TT from htop)]
    linarith [hb z.2 htop.2, (X.off_top j z htop).1]
  · rw [if_neg (show ¬(z.1 = false ∧ z.2 ∈ D.host.TT) from htop), zero_add]
    by_cases hthick : IsThickPl D z
    · linarith [(X.off_thick j z hthick).1]
    · exact (X.off_thin j z ⟨htop, hthick⟩).1

theorem kaJ_bounds (D : D7) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : 0 ≤ kaJ D j ∧ kaJ D j ≤ Nm D := by
  simp only [Formalism.BasicNotions.SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨h1, h2⟩ := hj
  have h1' : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have ht : (0 : ℝ) ≤ D.R.t + 1 := by positivity
  have hk : (0 : ℝ) ≤ D.R.k := by positivity
  unfold kaJ Nm Formalism.BasicNotions.Ranks.N
  push_cast
  constructor
  · apply div_nonneg _ (by norm_num)
    nlinarith
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (show 2 * (j : ℝ) - 1 ≤ 2 * D.R.m by linarith) ht]

theorem asksAll_of (X : Inst D L) (hSz : Nm D + 1 ≤ L.sc.w'' D.R.n) : RequiresAll X := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  intro a b ha hb p hp j hj s hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨hk0, hkN⟩ := kaJ_bounds D j hj
  have hNm0 : (0 : ℝ) ≤ Nm D := by unfold Nm; positivity
  have hwG : ∀ e, 1 ≤ fillG X b j (partner D p s e) := by
    intro e
    have := fill_ge X b hb j (partner D p s e)
    unfold fillG
    linarith
  have hw0 : ∀ e, 0 ≤ fillG X b j (partner D p s e) := fun e => by linarith [hwG e]
  have hwF : ∀ e, 0 ≤ fill X b j (partner D p s e) := fun e => by
    have := fill_ge X b hb j (partner D p s e)
    linarith
  have hA : 1 ≤ 2 * L.sc.a := by linarith
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg (by linarith) hA
  by_cases hy : 0 ≤ (a s : ℝ)
  · have h1 := shift_ge (p : ℝ) (a s) (kaJ D j) hp2 hk0 hy
      (fun e => fillG X b j (partner D p s e)) hw0 Odd
    have h2 := shift_le (p : ℝ) (a s) (kaJ D j) (2 * L.sc.a) hp2 hk0 hy (ha s hs) hA
      (fun e => fillG X b j (partner D p s e)) hwG Odd (fun e h => h)
    simp only [fillG, sub_add_cancel] at h1 h2
    unfold askP askG fillG
    refine ⟨h1, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hkN hlog]
  · have hz : ∀ c : ℕ → ℝ, (∀ e, 0 ≤ c e) →
        ∑' e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - c e) else 0) = 0 := by
      intro c hc
      refine (tsum_congr fun e => ?_).trans tsum_zero
      split_ifs
      · apply max_eq_left
        have : (a s : ℝ) / (p : ℝ) ^ e ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith [hc e]
      · rfl
    have e1 := hz (fun e => fill X b j (partner D p s e)) hwF
    have e2 := hz (fun e => fillG X b j (partner D p s e)) hw0
    beta_reduce at e1 e2
    unfold askP askG
    rw [e1, e2]
    exact ⟨le_rfl, by rw [zero_add]; exact mul_nonneg hNm0 hlog⟩

theorem lo_succ (K : Consts) (hLa : 0 ≤ K.La) (L : SizeData₂ D) (C bo : ℝ) (p : ℕ) (hp : p.Prime) :
    lo K L C bo p + (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ lo K L (C + 1) bo p := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  have hlogx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    show 0 ≤ L.sc.b' / (L.sc.x * D.R.n)
    exact div_nonneg hb'0 (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hd1 : 0 < L.sc.delta1 := by
    show 0 < L.sc.x ^ (-(L.sc.eps / 8))
    exact Real.rpow_pos_of_pos (by linarith) _
  have hLaS : 0 ≤ La K L.sc := by
    unfold La
    exact mul_nonneg (mul_nonneg hLa (by positivity)) (Real.log_nonneg ha1)
  have g1 : 0 ≤ (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hb'0) hlogx
  have g2 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
    div_nonneg (mul_nonneg hw hlogx) hd1.le
  have g3 : 0 ≤ La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) :=
    div_nonneg (mul_nonneg hLaS (by linarith)) (mul_nonneg hp0 (Nat.cast_nonneg _))
  have g4 : 0 ≤ L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hp0 _)
  have g5 : 0 ≤ L.sc.a / (p : ℝ) ^ 2 := div_nonneg (by linarith) (by positivity)
  have g6 := mul_nonneg hlogx (add_nonneg g3 g4)
  have g7 := mul_nonneg hlogx (add_nonneg g3 g5)
  obtain ⟨α, β, hform, hα⟩ : ∃ α β : ℝ, (∀ C' : ℝ, lo K L C' bo p = C' * α + β) ∧
      (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) ≤ α :=
    ⟨(cG L + L.etaSz) * Real.logb p (2 * L.sc.a) +
        (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then (rG L.sc : ℝ) * L.sc.b' * Real.log L.sc.x
          else if (p : ℝ) < L.sc.X' then L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 else 0)
          else 0) +
        (if IsResidueClassZero D p ∧ (p : ℝ) < L.sc.X' then Real.log L.sc.x * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
          (if (p : ℝ) < L.sc.p0 D.R.k then L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ))
            else L.sc.a / (p : ℝ) ^ 2)) else 0),
      (if IsResidueClassZero D p then (if (p : ℝ) < L.sc.p0 D.R.k then 0
        else if (p : ℝ) < L.sc.X' then L.sc.b' / L.sc.x + L.etaSz + bo else 0) else 0),
      fun C' => by
        simp only [lo]
        split_ifs <;> ring,
      by split_ifs <;> linarith [g1, g2, g6, g7]⟩
  rw [hform, hform]
  have e : (C + 1) * α + β = C * α + β + α := by ring
  rw [e]
  linarith

theorem fl_succ (D : D7) (s : Scale) (C : ℝ) (p : ℕ) (hp : p.Prime) : fl D s C p ≤ fl D s (C + 1) p := by
  have hx1 : 1 < s.x := s.one_lt_alt
  have hL0 : 0 ≤ s.L := by
    show 0 ≤ s.x ^ s.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ s.b := by
    show 1 ≤ Real.exp s.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ s.a := by
    show 1 ≤ s.x * s.b
    nlinarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl : 0 ≤ Real.logb p s.a := Real.logb_nonneg hp1 ha1
  have h1 : 0 ≤ (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a := mul_nonneg (by positivity) hl
  have h2 : 0 ≤ (D.R.f : ℝ) * Real.logb p s.a ^ 2 := by positivity
  unfold fl
  nlinarith [h1, h2]

theorem TTP_subset₂ (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : TTP X K a b p ⊆ D.host.TT := by
  unfold TTP
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem gainBoundAll_add_one_of_gainBoundAllRequired (X : Inst D L) (K : Consts) (hLa : 0 ≤ K.La) (C bo : ℝ) (hA : RequiresAll X) (hNc : Nm D ≤ cG L)
    (h : GainBoundAllUniform X K C bo) : GainBoundAll X K (C + 1) bo := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL0 : 0 ≤ L.sc.L := by
    show 0 ≤ L.sc.x ^ L.sc.eps
    exact Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ L.sc.b := by
    show 1 ≤ Real.exp L.sc.L
    exact Real.one_le_exp hL0
  have ha1 : 1 ≤ L.sc.a := by
    show 1 ≤ L.sc.x * L.sc.b
    nlinarith
  have hX1 : 1 ≤ L.sc.X' := by
    show 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3))
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hb'0 : 0 ≤ L.sc.b' := by
    show 0 ≤ L.sc.a / L.sc.X'
    exact div_nonneg (by linarith) (by linarith)
  intro a b hwin p hp hcls hX
  obtain ⟨hgain, hsum⟩ := h a b hwin p hp hcls hX
  refine ⟨hgain, ?_⟩
  have hlo := lo_succ K hLa L C bo p hp
  have hfl := fl_succ D L.sc C p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have heta := L.etaSz_pos
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hxA : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)
  have ha2 : ∀ t ∈ D.host.TT, (a t : ℝ) ≤ 2 * L.sc.a := by
    intro t ht
    have h1 := (hwin t ht).2.1
    have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
      div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hk1 hxA)
    linarith
  have hb0 : ∀ t ∈ D.host.TT, (0 : ℝ) ≤ (b t : ℝ) := fun t ht => by
    linarith [(hwin t ht).2.2]
  have hterm : ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ TTP X K a b p,
      askG X a b p j s - lo K L (C + 1) bo p ≤ askP X a b p j s - lo K L C bo p := by
    intro j hj s hs
    have hA := (hA a b ha2 hb0 p hp j hj s (TTP_subset₂ X K a b p hs)).2
    have h3 : Nm D * Real.logb p (2 * L.sc.a) ≤ (cG L + L.etaSz) * Real.logb p (2 * L.sc.a) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog
    linarith
  have hsum2 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askG X a b p j s - lo K L (C + 1) bo p)) ≤
      ∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p, (askP X a b p j s - lo K L C bo p) :=
    Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun s hs => hterm j hj s hs
  have hm : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hfl hm]

end Formalism.MainNotions.AuxBlock8.Pf.As

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

theorem mul_bound {s B c R : ℝ} (hs : s ≤ B) (hc : 0 ≤ c) (hBc : B * c ≤ R) : s * c ≤ R :=
  le_trans (mul_le_mul_of_nonneg_right hs hc) hBc

theorem rpow_neg_le_inv (s : Scale) (u : ℝ) (hu : u ≤ -1) : s.x ^ u ≤ 1 / s.x := by
  simpa [Real.rpow_neg_one, one_div] using Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu

theorem rpow_le_inv_of_le_neg_two (s : Scale) (h : 120 ≤ s.x) (u : ℝ) (hu : u ≤ -2) : s.x ^ u ≤ 1 / s.x / 120 := by
  have h1 := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le hu
  have hx := sc_x_pos s
  have h2 : s.x ^ (-2 : ℝ) = 1 / s.x / s.x := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  rw [h2] at h1
  refine le_trans h1 ?_
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h

theorem sum_low (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    {a b : HH D → ℤ} (h : InWin L a b) (hG : GainBoundAt X K C bo a b)
    (hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p)
    {A3 A4 PS : Finset ℕ} {badf : ℕ → ℝ} (T : Sets X K A3 A4 PS badf)
    (hZZ : WReq X K a b) (N : PrimeSumNumericFacts D L K C bo)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      47 / 10 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  have ha := sc_one_lt_a L.sc
  have hx := sc_x_pos L.sc
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hA : 0 ≤ L.sc.a / L.sc.x := div_nonneg (by linarith) hx.le
  have hX'' : 0 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  have hc1 := first_constant_nonneg L C hC
  have hc2 := second_constant_nonneg L C hC
  have hc3 := third_constant_nonneg L C bo hC hbo
  have hc4 := fourth_constant_nonneg K hK.1 L C hC
  have hcfl := cfl_nonneg D L.sc C hC
  refine le_trans (Finset.sum_le_sum (fun p hp =>
    low_le X K hK P C bo hC hbo h hG hSig T p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2)) ?_
  unfold E1
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have b1 : ∑ p ∈ S, (if p ∈ prB (L.sc.X'' D.R.n + 1) then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    have := card_prB_le (L.sc.X'' D.R.n + 1) (by linarith)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have b2 : ∑ p ∈ S, (if p ∈ prB (L.sc.p0 D.R.k) then Real.log p else 0) ≤ Real.log 4 * L.sc.p0 D.R.k :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (p0_pos D L.sc).le)
  have b3 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p else 0) ≤ Real.log 4 * L.sc.X' :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p) (fun p _ => Real.log_natCast_nonneg p))
      (sum_log_prB _ (by have := one_le_X' L.sc; linarith))
  have b4 : ∑ p ∈ S, (if p ∈ prB L.sc.X' then Real.log p / p else 0) ≤ lX L.sc :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (sum_logdiv_prB _ (one_le_X' L.sc))
  have b5 : ∑ p ∈ S, (if p ∈ A3 then Real.log p / p else 0) ≤ 1 / L.sc.x / 120 :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s3 (rpow_le_inv_of_le_neg_two _ N.n5 _ (by unfold Formalism.MainNotions.G.hG; have := L.sc.eps_pos; linarith)))
  have b6 : ∑ p ∈ S, (if p ∈ A4 then Real.log p / p else 0) ≤ 1 / L.sc.x :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p) (fun p _ => lp_nonneg p))
      (le_trans T.s4 (rpow_neg_le_inv _ _ le_rfl))
  have b7 : ∑ p ∈ S, (if p ∈ PS then Real.log p / p * badf p else 0) ≤
      (D.host.TT.card : ℝ) * (1 / L.sc.x / 120) :=
    le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * badf p)
      (fun p _ => mul_nonneg (lp_nonneg p) (T.hbad0 p)))
      (le_trans T.s2 (mul_le_mul_of_nonneg_left N.n7 hN))
  have b8 : ∑ p ∈ S, (if p ∈ _root_.Formalism.MainNotions.AuxBlock8.cands D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
      1 / L.sc.x / 120 := by
    refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
      (fun p hp => mul_nonneg (lp_nonneg p)
        (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
          (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
    exact le_trans ((WReq_iff X K a b).1 hZZ) (rpow_le_inv_of_le_neg_two L.sc N.n5 (-9) (by norm_num))
  have q1 := mul_bound b1 (add_nonneg (mul_nonneg hM hc1) (mul_nonneg hm hcfl))
    (R := 1 / 20 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n1 hM
      have e2 := mul_le_mul_of_nonneg_left N.n1' hm
      have e3 : (D.R.m : ℝ) * (L.sc.a / L.sc.x) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
        have := mul_le_mul_of_nonneg_left N.one_le_card_tops (mul_nonneg hm hA)
        nlinarith
      nlinarith)
  have q2 := mul_bound b2 (mul_nonneg hM hc2)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n2 hM
      linarith)
  have q3 := mul_bound b3 (mul_nonneg hM hc3)
    (R := 3 / 2 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n3 hM
      linarith)
  have q4 := mul_bound b4 (mul_nonneg hM hc4)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (by
      have e1 := mul_le_mul_of_nonneg_left N.n4 hM
      linarith)
  have hMa : 0 ≤ 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by positivity
  have q5 := mul_bound b5 hMa
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q6 := mul_bound b6 hMa
    (R := 3 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q7 := mul_bound b7 (by positivity : (0 : ℝ) ≤ 3 * (D.R.m : ℝ) * L.sc.a)
    (R := 1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have q8 := mul_bound b8 (by positivity : (0 : ℝ) ≤ 4 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a)
    (R := 1 / 30 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x))) (le_of_eq (by ring))
  have hU : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := mul_nonneg hM hA
  linarith

theorem sum_high (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C bo : ℝ) {a b : HH D → ℤ} (h : InWin L a b)
    (N : PrimeSumNumericFacts D L K C bo) (S : Finset ℕ) (hS : ∀ p ∈ S, L.sc.X'' D.R.n < (p : ℝ)) :
    ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤
      1 / 40 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by
  obtain ⟨hS1, hS2⟩ := Sc_facts P
  obtain ⟨hth0, hth1⟩ := thS_bounds P
  have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have := X'_le_X'' L.sc D.R.n (n_pos D); have := one_le_X' L.sc; linarith
  obtain ⟨ht0, ht1⟩ := thW_bounds D L.sc
  have hw := sc_w''_pos L.sc D.R.n (n_pos D)
  have hl2 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) *
      ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) := by positivity
  set R9 : Finset ℕ := Finset.Ioc ⌊L.sc.X'' D.R.n⌋₊ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ with hR9
  have hpt : ∀ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ (if p ∈ R9 then (1 : ℝ) else 0) *
      (Real.log (2 * L.sc.X'' D.R.n) * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc))) := by
    intro p hp
    have hpX := hS p hp
    have hd := dfc_high P X K h p hpX
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hlt : (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L)
    · rw [if_pos hlt] at hd
      have hmem : p ∈ R9 := by
        rw [hR9]
        refine Finset.mem_Ioc.2 ⟨(Nat.floor_lt (by linarith)).2 hpX, ?_⟩
        exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
      rw [if_pos hmem, one_mul]
      have h1 : max 0 (Dfc X K a b p) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc) :=
        max_le (by positivity) (by linarith)
      have h2 : Real.log p ≤ Real.log (2 * L.sc.X'' D.R.n) :=
        Real.log_le_log (by linarith) (by nlinarith)
      exact mul_le_mul h2 h1 (le_max_left _ _) hl2
    · rw [if_neg hlt] at hd
      have h1 : max 0 (Dfc X K a b p) = 0 := max_eq_left (by linarith)
      rw [h1, mul_zero]
      split_ifs
      · rw [one_mul]; exact hcoef
      · rw [zero_mul]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_mul]
  have b9 : ∑ p ∈ S, (if p ∈ R9 then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n * thS L + 2 := by
    refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hR9, Nat.card_Ioc]
    have hle : ⌊L.sc.X'' D.R.n⌋₊ ≤ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ :=
      le_trans (Nat.floor_le_floor (by nlinarith)) (Nat.floor_le_ceil _)
    rw [Nat.cast_sub hle]
    have h1 := Nat.ceil_lt_add_one (mul_nonneg (by linarith) (by linarith) : 0 ≤ L.sc.X'' D.R.n * (1 + thS L))
    have h2 := Nat.lt_floor_add_one (L.sc.X'' D.R.n)
    linarith
  refine mul_bound b9 hcoef ?_
  have e1 := mul_le_mul_of_nonneg_left N.n9 hM
  linarith

theorem inWin_of_box {K : Consts} {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) :
    InWin L a b := by
  classical
  intro t ht
  unfold box at ha hb
  have h1 := Fintype.mem_piFinset.1 ha t
  have h2 := Fintype.mem_piFinset.1 hb t
  rw [if_pos ht] at h1 h2
  unfold winA at h1
  unfold winB at h2
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.1 h1
  obtain ⟨h2a, _⟩ := Finset.mem_Icc.1 h2
  exact ⟨Int.ceil_le.1 h1a, Int.le_floor.1 h1b, Int.ceil_le.1 h2a⟩

theorem latticeChain_succ_of_partial (X : Inst D L) (K : Consts) (hK : K.Nonneg) (P : ParameterChoice' D L) (C bo : ℝ) (hC : 0 ≤ C) (hbo : 0 ≤ bo)
    (hG : GainBoundAll X K C bo) (hSig0 : ∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) (h2 : adm2 D L X) (h3 : adm3 D L)
    (h4 : ArchimedeanSignatureMatching D L K) (N : PrimeSumNumericFacts D L K C bo) : PointsLemma D L X K := by
  classical
  intro a ha b hb hZZ
  have hW := inWin_of_box ha hb
  have hSig : ∀ p, Cand D L K p → 0 ≤ Sig X K a b p := fun p hp => hSig0 a b p hp
  have hXX := X'_le_X'' L.sc D.R.n (n_pos D)
  have h2' := h2.2
  unfold BTT at h2'
  unfold adm3 at h3
  have h4' := h4.2.2.2.2
  have T : Sets X K _ _ _ (fun p => ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)) :=
    { hA3 := fun p hp hc hX ho => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 (by linarith)), hp, by linarith, hc⟩, ho⟩
      hA4 := fun p hp hX hB => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hX), hp, hB⟩
      hPS := fun p hC => Finset.mem_filter.2 ⟨by
          unfold primesResidueBelow
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_ceil.2 hC.2.1), hC.1, hC.2.1, hC.2.2.1⟩, hC.2.2.2.1⟩
      hPSsub := fun p hp => by
          have h1 := (Finset.mem_filter.1 hp).1
          unfold primesResidueBelow at h1
          have h2 := (Finset.mem_filter.1 h1).2
          exact mem_prB.2 ⟨h2.1, h2.2.1⟩
      hbad := fun p _ => by
          have : (D.host.TT \ D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ goodReps X p)) ⊆
              D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t)) := by
            intro t ht
            obtain ⟨ht1, ht2⟩ := Finset.mem_sdiff.1 ht
            refine Finset.mem_filter.2 ⟨ht1, fun hg => ht2 (Finset.mem_filter.2 ⟨ht1, ?_⟩)⟩
            unfold goodReps reps
            exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩
          exact_mod_cast Finset.card_le_card this
      hbad0 := fun p => Nat.cast_nonneg _
      s3 := h3
      s4 := h4'
      s2 := h2' }
  refine ⟨?_, ?_⟩
  · intro S hS
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n)
      (fun p : ℕ => Real.log p * max 0 (Dfc X K a b p))
    have l1 := sum_low X K hK P C bo hC hbo hW (hG a b hW) hSig T hZZ N
      (S.filter (fun p : ℕ => (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => ⟨(hS p (Finset.mem_filter.1 hp).1).1, (hS p (Finset.mem_filter.1 hp).1).2, (Finset.mem_filter.1 hp).2⟩)
    have l2 := sum_high P X K C bo hW N (S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L.sc.X'' D.R.n))
      (fun p hp => not_le.1 (Finset.mem_filter.1 hp).2)
    have hMA : 0 ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x) := by
      have := sc_one_lt_a L.sc
      have := sc_x_pos L.sc
      positivity
    have e : 5 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / L.sc.x =
        5 * ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (L.sc.a / L.sc.x)) := by ring
    rw [e]
    change ∑ p ∈ S, Real.log p * max 0 (Dfc X K a b p) ≤ _
    linarith
  · intro S _
    have hMa : 0 ≤ ((D.R.m : ℝ) * (D.host.TT.card : ℝ)) * L.sc.a := by
      have := sc_one_lt_a L.sc
      positivity
    refine le_trans (Finset.sum_le_sum (fun p _ => io_le X K hK P hW hSig p)) ?_
    rw [← Finset.sum_mul]
    have b8 : ∑ p ∈ S, (if p ∈ _root_.Formalism.MainNotions.AuxBlock8.cands D L K then Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p) else 0) ≤
        L.sc.x ^ (-9 : ℝ) := by
      refine le_trans (sum_ite_mem_le (fun p : ℕ => Real.log p / p * (2 * dropI X K a b p + 4 * Sig X K a b p))
        (fun p hp => mul_nonneg (lp_nonneg p)
          (add_nonneg (mul_nonneg (by norm_num) (dropI_nonneg X K a b p))
            (mul_nonneg (by norm_num) (hSig p (cand_of_mem hp)))))) ?_
      exact (WReq_iff X K a b).1 hZZ
    exact mul_bound b8 hMa (le_of_eq (by ring))

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NinthBoundArithB =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NinthBoundArithB", "h": "module\n\npublic import Mathlib.Analysis.Complex.Exponential\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\npublic import Mathlib.Analysis.Complex.ExponentialBounds\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

theorem forty_le_exp_four : (40 : ℝ) ≤ Real.exp 4 := by
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (40 : ℝ) ≤ (27 / 10) ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4

theorem ninth_bound_arith_b (Xpp θ lg w a x S Y X' b : ℝ) (hXw : Xpp * w = a) (hab : a = x * b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 2 * x) (hlgY : lg ≤ Y) (hw1 : 1 ≤ w) (hwa : w ≤ a) (hx : 0 < x)
    (hq : 480 * x ^ 2 * θ ≤ 1) (hS0 : 0 ≤ S) (hSY : S ≤ Y) (hY : 10 ≤ Y) (hX1 : 1 ≤ Xpp) (hXY : Xpp ≤ X' * Y)
    (hX'0 : 0 ≤ X') (e7 : Y ^ 7 * X' ≤ b) :
    (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) ≤ b / 40 := by
  have hw0 : 0 < w := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hXp0 : 0 ≤ Xpp := by linarith
  have hb0 : 0 ≤ b := le_trans (by positivity) e7
  have ha0 : 0 ≤ a := by rw [hab]; positivity
  have e : (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) =
      lg * ((Xpp * w) * θ ^ 2 + 2 * θ * w) +
        lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) := by
    field_simp
    ring
  rw [e, hXw]
  have t1 : a * θ ^ 2 + 2 * θ * w ≤ 3 * a * θ := by
    nlinarith [mul_nonneg (mul_nonneg ha0 hθ0) (sub_nonneg.2 hθ1), mul_nonneg hθ0 (sub_nonneg.2 hwa)]
  have t10 : 0 ≤ a * θ ^ 2 + 2 * θ * w := by positivity
  have T1 : lg * (a * θ ^ 2 + 2 * θ * w) ≤ b / 80 := by
    calc lg * (a * θ ^ 2 + 2 * θ * w) ≤ (2 * x) * (3 * a * θ) := mul_le_mul hlg t1 t10 (by positivity)
      _ = (480 * x ^ 2 * θ) * (b / 80) := by rw [hab]; ring
      _ ≤ 1 * (b / 80) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = b / 80 := one_mul _
  have hXw' : Xpp / w ≤ Xpp := div_le_self hXp0 hw1
  have hXw0 : 0 ≤ Xpp / w := by positivity
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have a0 : Xpp * θ ≤ Xpp := by nlinarith
  have a1 : (Xpp * θ + 2) * S ≤ (3 * Xpp) * Y := mul_le_mul (by linarith) hSY hS0 (by linarith)
  have a2 : 3 * S * Xpp * θ ≤ 3 * Y * Xpp := by
    have h1 : 3 * S * Xpp ≤ 3 * Y * Xpp := by gcongr
    have h2 : 3 * S * Xpp * θ ≤ 3 * S * Xpp * 1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
    linarith
  have a3 : 3 * S ^ 2 * (Xpp / w) ≤ 3 * Y ^ 2 * Xpp := by gcongr
  have a4 : Y * Xpp ≤ Y ^ 2 * Xpp := mul_le_mul_of_nonneg_right hYY hXp0
  have t2 : (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) ≤ 9 * Y ^ 2 * Xpp := by linarith
  have t20 : 0 ≤ (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) := by positivity
  have T2 : lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ b / 80 := by
    have h3 : (1000 : ℝ) ≤ Y ^ 3 := by
      calc (1000 : ℝ) = 10 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY 3
    have h4 : 0 ≤ Y ^ 4 * X' := by positivity
    have h5 : 720 * (Y ^ 4 * X') ≤ Y ^ 7 * X' := by
      calc 720 * (Y ^ 4 * X') ≤ Y ^ 3 * (Y ^ 4 * X') := mul_le_mul_of_nonneg_right (by linarith) h4
        _ = Y ^ 7 * X' := by ring
    calc lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ Y * (9 * Y ^ 2 * Xpp) :=
          mul_le_mul hlgY t2 t20 hY0
      _ ≤ Y * (9 * Y ^ 2 * (X' * Y)) := by gcongr
      _ = 9 * (Y ^ 4 * X') := by ring
      _ ≤ b / 80 := by linarith
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NinthBoundArithB =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NinthBoundArithB\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

structure NumG5' (D : D7) (L : SizeData₂ D) (K : Consts) (C bo : ℝ) : Prop where
  one_le_card_tops : (1 : ℝ) ≤ (D.host.TT.card : ℝ)
  n1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x
  n1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.a / L.sc.x
  n2 : Real.log 4 * L.sc.p0 D.R.k * c2 L C ≤ L.sc.a / L.sc.x
  n3 : Real.log 4 * L.sc.X' * c3 L C bo ≤ 3 / 2 * (L.sc.a / L.sc.x)
  n4 : (Real.log L.sc.X' * (1 + Real.log L.sc.X')) * c4 K L C ≤ L.sc.a / L.sc.x
  n5 : 120 ≤ L.sc.x
  n7 : L.sc.x ^ (-2 + L.sc.eps) ≤ 1 / L.sc.x / 120
  n9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a / L.sc.x / 40

theorem zz_arith (z : ℝ) (h : 1 ≤ z) : z * (1 + z) ≤ 2 * (z * z) := by nlinarith


theorem prime_sum_facts_eventually (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → adm5 D L K (eps / 48) → NumG5' D L K C (L.sc.b ^ (x ^ (-(eps / 2)))) := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have hτ : 0 < 23 * eps / 48 := by positivity
  have F1 := ev_log 14 (23 * eps / 48) hτ
  have F2 := ev_const C (23 * eps / 48) hτ
  have F3 := ev_const 10 (23 * eps / 48) hτ
  have F4 := ev_log 1 eps he0
  have F5 := ev_pow 3 eps 1 (by linarith)
  have F6 := ev_pow 14 (23 * eps / 48) eps (by linarith)
  have F7 := ev_pow 4 (eps / 3) eps (by linarith)
  have F8 := ev_pow 4 (eps / 4) eps (by linarith)
  have F9 := ev_pow 4 (eps / 2) eps (by linarith)
  have WorkedExample := ev_pow 8 0 eps he0
  have LargeParameterEstimates := ev_log 40 (eps / 3) (by positivity)
  have F12 := ev_log (2 * (Real.log 4 * C * (rE eps : ℝ))) 1 one_pos
  have InertPlaceConditions := ev_log (2 * (Real.log 4 * C)) 1 one_pos
  have F14 := ev_log (40 * C) 1 one_pos
  have F15 := ev_log (4 * C) 1 one_pos
  have F16 := ev_pow 120 eps 1 (by linarith)
  have F17 := ev_log 5 1 one_pos
  filter_upwards [F1, F2, F3, F4, F5, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12, InertPlaceConditions, F14, F15, F16, F17,
    eventually_ge_atTop 16, eventually_ge_atTop 120] with x f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 hx16
    hx120 D L hx heps hS P h5
  clear F1 F2 F3 F4 F5 F6 F7 F8 F9 WorkedExample LargeParameterEstimates F12 InertPlaceConditions F14 F15 F16 F17
  subst hx
  subst heps
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := by linarith only [hk1]
  obtain ⟨_, hNmSc, hSc100⟩ := Nm_le_Sc P
  obtain ⟨hSN, hSM, hSK, -, -, -, -, hSTT, -, -, -, -, -, hSEta, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  unfold Formalism.MainNotions.SizeTT Formalism.MainNotions.szNst Formalism.MainNotions.szTh at hSTT
  unfold Formalism.MainNotions.SizeEta at hSEta
  unfold Formalism.MainNotions.SizeDel at hSDel
  rw [Real.rpow_one] at f5 f12 f13 f14 f15 f16 f17
  rw [Real.rpow_zero] at f10
  have mono : ∀ u v : ℝ, u ≤ v → L.sc.x ^ u ≤ L.sc.x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have nat4 : L.sc.x ^ (4 : ℝ) = L.sc.x ^ 4 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat6 : L.sc.x ^ (6 : ℝ) = L.sc.x ^ 6 := by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA : L.sc.x ^ Scale.A = L.sc.x ^ 26 := by
    unfold Scale.A; rw [show (26 : ℝ) = ((26 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA2 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    unfold Scale.A; rw [show (26 / 2 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by rw [← nat3]; exact le_trans hSN.2 (mono _ _ (by linarith only [he0, he1]))
  have hn2 : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by rw [← nat2]; exact le_trans (mono _ _ (by linarith only [he0, he1])) hSN.1
  have hk4 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by rw [← nat4]; exact le_trans (mono _ _ (by linarith only [he0, he1])) hSK.1
  rw [nat6] at hk6
  have hn0 : (0 : ℝ) < (D.R.n : ℝ) := lt_of_lt_of_le (by positivity) hn2
  have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le he0.le
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hb0 : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha0 : 0 < L.sc.a := by rw [ha]; positivity
  have hax : L.sc.a / L.sc.x = L.sc.b := by rw [ha]; field_simp
  have hXd : L.sc.X' = Real.exp (L.sc.x ^ (L.sc.eps / 3)) := rfl
  have hX0 : 0 < L.sc.X' := by rw [hXd]; exact Real.exp_pos _
  have hX1 : 1 ≤ L.sc.X' := by rw [hXd]; exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'X : L.sc.b' * L.sc.X' = L.sc.x * L.sc.b := by
    unfold Scale.b'; rw [div_mul_cancel₀ _ hX0.ne', ha]
  have hb'0 := sc_b'_nonneg L.sc
  have hXpp : L.sc.X'' D.R.n = L.sc.X' * (L.sc.x * (D.R.n : ℝ)) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  have hlogX : Real.log L.sc.X' = L.sc.x ^ (L.sc.eps / 3) := by rw [hXd, Real.log_exp]

  have hY10 : 10 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := f3
  have hY0 : 0 < (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_pos _
  have pY : ∀ q : ℝ, ∀ M : ℕ, q ≤ L.sc.x ^ M → M ≤ 14 → q ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro q M hq hM
    refine le_trans hq ?_
    rw [← Real.rpow_natCast]
    apply xpow_le_exp _ _ _ hx0
    have : (M : ℝ) ≤ 14 := by exact_mod_cast hM
    exact le_trans (mul_le_mul_of_nonneg_right this hlx0) f1
  have e_eta : L.etaSz ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc L.etaSz ≤ Real.exp (Real.log L.etaSz) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.exp_le_exp.2 hSEta.2.2.1
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 (mono _ _ (by linarith only [he0, he1]))
  have hT4 : L.sc.x ^ (L.sc.eps / 4) ≤ (L.sc.x ^ (23 * L.sc.eps / 48)) := mono _ _ (by linarith only [he0, he1])
  have e_Del : (D.s.Del : ℝ) ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
    calc (D.s.Del : ℝ) ≤ Real.exp (Real.log (D.s.Del : ℝ)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := Real.exp_le_exp.2 hSDel.2.2.1
      _ ≤ _ := Real.exp_le_exp.2 (by linarith only [hT4])
  have hDel0 : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    have h := L.Sc_eq
    by_contra hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le (by linarith only [not_le.1 hneg])
    linarith only [h, this, hSc100]
  have h7 : L.sc.x * L.sc.x ^ 6 ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := by
    have : L.sc.x * L.sc.x ^ 6 = L.sc.x ^ ((7 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
    rw [this]
    apply xpow_le_exp _ _ _ hx0
    push_cast
    linarith only [f1]
  have hcG0 : 0 ≤ cG L := by unfold cG; linarith only [hSc100]
  have e_c : cG L ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc cG L = (16 * (D.R.k : ℝ)) * (D.s.Del : ℝ) := by unfold cG; rw [L.Sc_eq]; ring
      _ ≤ (L.sc.x * L.sc.x ^ 6) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
          mul_le_mul (mul_le_mul hx16 hk6 hk0.le hx0.le) e_Del hDel0 (by positivity)
      _ ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [← Real.exp_add]; congr 1; ring
  have e_Nm : Nm D ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have : Nm D ≤ cG L := by unfold Nm cG; linarith only [hNmSc, hSc100]
    exact le_trans this e_c
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have e_xn : L.sc.x * (D.R.n : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 4 (le_trans (mul_le_mul_of_nonneg_left hn3 hx0.le) (le_of_eq (by ring))) (by norm_num)
  have e_f : (D.R.f : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by unfold Ranks.f; push_cast; ring
    rw [hf]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith only [hx16]) hn0.le) e_xn
  have hla : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hxY : L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 1 (by rw [pow_one]) (by norm_num)
  have e_la : Real.log L.sc.a ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [hla]; linarith only [hxY, f4, f5, hxe1]
  have hla0 : 0 ≤ Real.log L.sc.a := by rw [hla]; linarith only [hlx0, hxe1]
  have e_la2 : Real.log (2 * L.sc.a) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    rw [Real.log_mul (by norm_num) ha0.ne', hla]
    have := Real.log_two_lt_d9
    linarith only [this, hxY, f4, f5, hxe1]
  have hla20 : 0 ≤ Real.log (2 * L.sc.a) := Real.log_nonneg (by have := sc_one_lt_a L.sc; linarith only [this])
  have e7 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 7 * L.sc.X' ≤ L.sc.b := by
    rw [hb, hXd, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    linarith only [f6, f7, hxe1]
  have hz1 : 1 ≤ L.sc.x ^ (L.sc.eps / 3) := Real.one_le_rpow hx1.le (by positivity)
  have hzz : L.sc.x ^ (L.sc.eps / 3) * (1 + L.sc.x ^ (L.sc.eps / 3)) ≤ 2 * L.sc.x ^ (2 * L.sc.eps / 3) := by
    have : L.sc.x ^ (2 * L.sc.eps / 3) = L.sc.x ^ (L.sc.eps / 3) * L.sc.x ^ (L.sc.eps / 3) := by rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]
    exact zz_arith _ hz1
  have hzx : L.sc.x ^ (2 * L.sc.eps / 3) ≤ L.sc.x := by
    have := mono (2 * L.sc.eps / 3) 1 (by linarith only [he0, he1])
    rwa [Real.rpow_one] at this
  have hl4 : Real.log 4 ≤ 1387 / 1000 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith only [this, h]
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hx120, ?_, ?_⟩
  ·
    refine le_trans ?_ hSTT.1
    have h1 : L.sc.x ^ (-(L.sc.eps / 100)) * L.sc.x ^ (2 + 8 * L.sc.eps - L.sc.eps / 100) * L.sc.delta1 ≤
        L.sc.x ^ (-(L.sc.eps / 100)) * (D.R.n : ℝ) * L.sc.delta1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSN.1 (Real.rpow_nonneg hx0.le _))
        (sc_delta1_pos L.sc).le
    refine le_trans ?_ h1
    unfold Scale.delta1
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    exact Real.one_le_rpow hx1.le (by linarith only [he0, he1])
  ·
    rw [hax, hXpp]
    unfold c1
    exact first_bound_arith C (cG L) L.etaSz _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC hcG0 L.etaSz_pos.le hla20 (by positivity) f2 e_c e_eta e_la2 e_xn
      hX1 hY10 e7
  ·
    rw [hax, hXpp]
    unfold cfl
    exact n1'_arith C _ (Nm D) _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC (Nat.cast_nonneg _) hNm0 hla0 (by positivity) f2 e_f e_Nm e_la e_xn
      hX1 hY10 e7
  ·
    rw [hax]
    unfold c2 Scale.p0
    rw [natA, rG_rE]
    have hW1 : (1 : ℝ) ≤ L.sc.x ^ 26 := one_le_pow₀ hx1.le
    have hW2 : L.sc.x ^ 2 ≤ L.sc.x ^ 26 := pow_le_pow_right₀ hx1.le (by norm_num)
    have hX40 : (D.R.k : ℝ) ^ 2 * L.sc.x ^ 26 * L.sc.x * L.sc.x ≤ L.sc.X' := by
      have h1 : (D.R.k : ℝ) ^ 2 ≤ (L.sc.x ^ 6) ^ 2 := pow_le_pow_left₀ hk0.le hk6 2
      have h2 : (D.R.k : ℝ) ^ 2 * L.sc.x ^ 26 * L.sc.x * L.sc.x ≤ (L.sc.x ^ 6) ^ 2 * L.sc.x ^ 26 * L.sc.x * L.sc.x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (pow_pos hx0 26).le) hx0.le) hx0.le
      have h3 : (L.sc.x ^ 6) ^ 2 * L.sc.x ^ 26 * L.sc.x * L.sc.x = L.sc.x ^ ((40 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
      rw [h3] at h2
      refine le_trans h2 ?_
      rw [hXd]
      apply xpow_le_exp _ _ _ hx0
      push_cast
      exact f11
    have t1 := second_bound_arith_a (Real.log 4 * C * (rE L.sc.eps : ℝ) * Real.log L.sc.x) (D.R.k : ℝ) (L.sc.x ^ 26) L.sc.x L.sc.b' L.sc.X' L.sc.b
      (by linarith only [f12]) hx0 (by positivity) hb'0 hX40 hb'X
    have t2 := second_bound_arith_b (Real.log 4 * C * Real.log L.sc.x) (D.R.k : ℝ) (L.sc.x ^ 26) L.sc.x L.sc.b
      (by linarith only [f13]) hx0 hk1 hW2 hW1 hb0.le
    rw [ha]
    have e0 : Real.log 4 * ((D.R.k : ℝ) ^ 2 * L.sc.x ^ 26) * (C * (rE L.sc.eps : ℝ) * L.sc.b' * Real.log L.sc.x +
        C * Real.log L.sc.x * (L.sc.x * L.sc.b * (((D.R.k : ℝ) * L.sc.x ^ 26) ^ 4)⁻¹)) =
        Real.log 4 * C * (rE L.sc.eps : ℝ) * Real.log L.sc.x * ((D.R.k : ℝ) ^ 2 * L.sc.x ^ 26) * L.sc.b' +
        Real.log 4 * C * Real.log L.sc.x * ((D.R.k : ℝ) ^ 2 * L.sc.x ^ 26) *
          (L.sc.x * L.sc.b * (((D.R.k : ℝ) * L.sc.x ^ 26) ^ 4)⁻¹) := by ring
    rw [e0]
    exact le_trans (add_le_add t1 t2) (le_of_eq (by ring))
  ·
    rw [hax]
    unfold c3
    have hbo : L.sc.b ^ (L.sc.x ^ (-(L.sc.eps / 2))) = Real.exp (L.sc.x ^ (L.sc.eps / 2)) := by
      rw [hb, ← Real.exp_mul, ← Real.rpow_add hx0]
      congr 2
      ring
    rw [hbo]
    have h3e : (40 : ℝ) ≤ Real.exp 4 := forty_le_exp_four
    have u0 : L.sc.X' * (L.sc.b' / L.sc.x) = L.sc.b := by
      have : L.sc.X' * (L.sc.b' / L.sc.x) = (L.sc.b' * L.sc.X') / L.sc.x := by ring
      rw [this, hb'X]; field_simp
    have u1 : 40 * (L.sc.X' * L.etaSz) ≤ L.sc.b := by
      have hη : L.etaSz ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) :=
        le_trans (Real.le_exp_log _) (Real.exp_le_exp.2 hSEta.2.2.1)
      calc 40 * (L.sc.X' * L.etaSz) ≤ Real.exp 4 * (Real.exp (L.sc.x ^ (L.sc.eps / 3)) * Real.exp (L.sc.x ^ (L.sc.eps / 4))) := by
            rw [hXd]
            exact mul_le_mul h3e (mul_le_mul_of_nonneg_left hη (Real.exp_pos _).le)
              (mul_nonneg (Real.exp_pos _).le L.etaSz_pos.le) (Real.exp_pos _).le
        _ = Real.exp (4 + (L.sc.x ^ (L.sc.eps / 3) + L.sc.x ^ (L.sc.eps / 4))) := by rw [Real.exp_add, Real.exp_add]
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.2 (by linarith only [f7, f8, f10])
    have u2 : 40 * (L.sc.X' * Real.exp (L.sc.x ^ (L.sc.eps / 2))) ≤ L.sc.b := by
      calc 40 * (L.sc.X' * Real.exp (L.sc.x ^ (L.sc.eps / 2))) ≤
            Real.exp 4 * (Real.exp (L.sc.x ^ (L.sc.eps / 3)) * Real.exp (L.sc.x ^ (L.sc.eps / 2))) := by
            rw [hXd]
            exact mul_le_mul_of_nonneg_right h3e (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        _ = Real.exp (4 + (L.sc.x ^ (L.sc.eps / 3) + L.sc.x ^ (L.sc.eps / 2))) := by rw [Real.exp_add, Real.exp_add]
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.2 (by linarith only [f7, f9, f10])
    have u3 : 40 * (L.sc.X' * (C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1)) ≤ L.sc.b := by
      have hd : 1 / L.sc.delta1 = L.sc.x ^ (L.sc.eps / 8) := by
        unfold Scale.delta1
        rw [Real.rpow_neg hx0.le, one_div, inv_inv]
      have hXw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / (D.R.n : ℝ) := by
        unfold Scale.w''
        have : L.sc.X' * (L.sc.b' / (L.sc.x * (D.R.n : ℝ))) = (L.sc.b' * L.sc.X') / (L.sc.x * (D.R.n : ℝ)) := by ring
        rw [this, hb'X]; field_simp
      have h8 : L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x := by
        have := mono (L.sc.eps / 8) 1 (by linarith only [he0, he1])
        rwa [Real.rpow_one] at this
      have h80 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := Real.rpow_nonneg hx0.le _
      have e1 : 40 * (L.sc.X' * (C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1)) =
          (40 * C * Real.log L.sc.x * (1 / L.sc.delta1)) * (L.sc.X' * L.sc.w'' D.R.n) := by ring
      rw [e1, hd, hXw]
      have h1 : 40 * C * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) ≤ (D.R.n : ℝ) := by
        calc 40 * C * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x * L.sc.x := mul_le_mul f14 h8 h80 hx0.le
          _ = L.sc.x ^ 2 := by ring
          _ ≤ _ := hn2
      calc 40 * C * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) * (L.sc.b / (D.R.n : ℝ)) ≤ (D.R.n : ℝ) * (L.sc.b / (D.R.n : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = L.sc.b := by field_simp
    have e2 : Real.log 4 * L.sc.X' * (L.sc.b' / L.sc.x + L.etaSz + C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 +
        Real.exp (L.sc.x ^ (L.sc.eps / 2))) = Real.log 4 * (L.sc.X' * (L.sc.b' / L.sc.x) + L.sc.X' * L.etaSz +
          L.sc.X' * (C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) + L.sc.X' * Real.exp (L.sc.x ^ (L.sc.eps / 2))) := by ring
    rw [e2, u0]
    have h2b : L.sc.b + L.sc.X' * L.etaSz + L.sc.X' * (C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) +
        L.sc.X' * Real.exp (L.sc.x ^ (L.sc.eps / 2)) ≤ 43 / 40 * L.sc.b := by linarith only [u1, u2, u3]
    calc _ ≤ Real.log 4 * (43 / 40 * L.sc.b) := mul_le_mul_of_nonneg_left h2b hl40
      _ ≤ 1387 / 1000 * (43 / 40 * L.sc.b) := mul_le_mul_of_nonneg_right hl4 (by positivity)
      _ ≤ 3 / 2 * L.sc.b := by linarith only [hb0]
  ·
    rw [hlogX]
    unfold c4
    have hLa0 : 0 ≤ La K L.sc := by
      unfold La; exact mul_nonneg (mul_nonneg hK.1 (by positivity)) hla0
    have hLa1 : La K L.sc ≤ L.sc.x := by
      have := mono (L.sc.eps + L.sc.eps / 48) 1 (by linarith only [he0, he1])
      rw [Real.rpow_one] at this
      exact le_trans h5.2.1 this
    have hp0 : L.sc.x ^ 3 ≤ L.sc.p0 D.R.k := by
      unfold Scale.p0
      rw [natA]
      have h1 : L.sc.x ^ 3 ≤ L.sc.x ^ 26 := pow_le_pow_right₀ hx1.le (by norm_num)
      have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := one_le_pow₀ hk1
      calc L.sc.x ^ 3 ≤ 1 * L.sc.x ^ 26 := by rw [one_mul]; exact h1
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 (pow_pos hx0 26).le
    exact fourth_bound_arith _ C _ _ _ _ _ L.sc.x hC hlx0 hLa0 ha0.le hx0 hk0 (by linarith only [hzz, hzx]) f15
      (le_trans (mul_le_mul_of_nonneg_right hLa1 (pow_pos hx0 3).le) (le_trans (le_of_eq (by ring)) hk4)) hp0
  ·
    have h2 : L.sc.x ^ (-2 + L.sc.eps) = L.sc.x ^ L.sc.eps * (L.sc.x ^ 2)⁻¹ := by
      rw [add_comm, Real.rpow_add hx0, Real.rpow_neg hx0.le, nat2]
    rw [h2]
    have h3 : L.sc.x ^ L.sc.eps ≤ L.sc.x / 120 := by linarith only [f16]
    calc L.sc.x ^ L.sc.eps * (L.sc.x ^ 2)⁻¹ ≤ L.sc.x / 120 * (L.sc.x ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 1 / L.sc.x / 120 := by field_simp
  ·
    have hw0 := sc_w''_nonneg L.sc D.R.n
    obtain ⟨hw1, hw2⟩ := w''_le L.sc D.R.n (Nat.cast_pos.1 hn0)
    have hab := two_b'_le_a L.sc
    have hwpos : 0 < L.sc.w'' D.R.n := by
      unfold Scale.w'' Scale.b'; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.a := by
      unfold Scale.X''; exact div_mul_cancel₀ _ hwpos.ne'
    have hq : 480 * L.sc.x ^ 2 ≤ (D.R.k : ℝ) * L.sc.x ^ 13 := by
      have h0 : 480 ≤ L.sc.x * L.sc.x := le_trans (by norm_num) (mul_le_mul hx120 hx120 (by norm_num) hx0.le)
      have h1 : 480 * L.sc.x ^ 2 ≤ (L.sc.x * L.sc.x) * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right h0 (by positivity)
      have h2 : (L.sc.x * L.sc.x) * L.sc.x ^ 2 = L.sc.x ^ 4 := by ring
      have h3 : L.sc.x ^ 4 ≤ L.sc.x ^ 13 := pow_le_pow_right₀ hx1.le (by norm_num)
      calc 480 * L.sc.x ^ 2 ≤ L.sc.x ^ 4 := by rw [← h2]; exact h1
        _ ≤ 1 * L.sc.x ^ 13 := by rw [one_mul]; exact h3
        _ ≤ _ := mul_le_mul_of_nonneg_right hk1 (pow_pos hx0 13).le
    have hq1 : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ 13 := one_le_mul_of_one_le_of_one_le hk1 (one_le_pow₀ hx1.le)
    have hθ : thW D L.sc = 1 / ((D.R.k : ℝ) * L.sc.x ^ 13) := by unfold thW; rw [natA2]
    have hlg : Real.log (2 * L.sc.X'' D.R.n) ≤ 2 * L.sc.x := by
      rw [hXpp, show 2 * (L.sc.X' * (L.sc.x * (D.R.n : ℝ))) = L.sc.X' * (2 * (L.sc.x * (D.R.n : ℝ))) by ring,
        Real.log_mul hX0.ne' (by positivity), hlogX]
      have h1 : 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        have h0 := mul_le_mul_of_nonneg_left hn3 hx0.le
        calc 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x * (L.sc.x * L.sc.x ^ 3) :=
              mul_le_mul (by linarith only [hx16]) h0 (by positivity) hx0.le
          _ = L.sc.x ^ 5 := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hx0] at h2
      push_cast at h2
      have h3 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x := by
        have := mono (L.sc.eps / 3) 1 (by linarith only [he0, he1])
        rwa [Real.rpow_one] at this
      linarith only [h2, h3, f17]
    have hlg0 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := by
      apply Real.log_nonneg
      rw [hXpp]
      have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
      have := one_le_mul_of_one_le_of_one_le hX1 (one_le_mul_of_one_le_of_one_le hx1.le hn1)
      linarith only [this]
    obtain ⟨hSc1, hSc2⟩ := Sc_facts P
    have hXpp1 : 1 ≤ L.sc.X'' D.R.n := by
      rw [hXpp]
      have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
      exact one_le_mul_of_one_le_of_one_le hX1 (one_le_mul_of_one_le_of_one_le hx1.le hn1)
    have h2xY : 2 * L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
      pY _ 2 (by rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith only [hx16]) hx0.le) (by norm_num)
    rw [hax]
    unfold thS
    exact ninth_bound_arith_b _ _ _ _ L.sc.a L.sc.x L.Sc (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) L.sc.X' L.sc.b hXw ha
      (by rw [hθ]; positivity) (by rw [hθ, div_le_one (by linarith only [hq1])]; exact hq1) hlg0 hlg (le_trans hlg h2xY)
      (by linarith only [hSc1, hSc2]) (by linarith only [hw1, hw2, hab, hb'0]) hx0
      (by rw [hθ, mul_one_div, div_le_one (by linarith only [hq1])]; exact hq) (by linarith only [hSc1])
      (by unfold cG at e_c; linarith only [e_c, hSc1]) hY10 hXpp1
      (by rw [hXpp]; exact mul_le_mul_of_nonneg_left e_xn hX0.le) hX0.le e7

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

theorem prime_sum_facts_of_scaled {D : D7} {L : SizeData₂ D} {K : Consts} {C bo : ℝ} (hC : 0 ≤ C) (N : Nu.NumG5' D L K (40 * C) bo) :
    PrimeSumNumericFacts D L K C bo := by
  have e1 : c1 L (40 * C) = 40 * c1 L C := by unfold c1; ring
  have e1' : cfl D L.sc (40 * C) = 40 * cfl D L.sc C := by unfold cfl; ring
  have e2 : c2 L (40 * C) = 40 * c2 L C := by unfold c2; ring
  have e4 : c4 K L (40 * C) = 40 * c4 K L C := by unfold c4; ring
  have e3 : c3 L C bo ≤ c3 L (40 * C) bo := by
    unfold c3
    have h0 : 0 ≤ L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 :=
      div_nonneg (mul_nonneg (sc_w''_nonneg _ _) (logx_nonneg _)) (sc_delta1_pos _).le
    have h1 : C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 = C * (L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1) := by
      ring
    have h2 : 40 * C * L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1 =
        40 * (C * (L.sc.w'' D.R.n * Real.log L.sc.x / L.sc.delta1)) := by ring
    rw [h1, h2]
    have := mul_nonneg hC h0
    linarith
  have n1 := N.n1
  have n1' := N.n1'
  have n2 := N.n2
  have n4 := N.n4
  rw [e1] at n1
  rw [e1'] at n1'
  rw [e2] at n2
  rw [e4] at n4
  have hl4X : 0 ≤ Real.log 4 * L.sc.X' :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (le_trans zero_le_one (one_le_X' L.sc))
  refine ⟨N.one_le_card_tops, by linarith, by linarith, by linarith,
    le_trans (mul_le_mul_of_nonneg_left e3 hl4X) N.n3, ?_, N.n5, N.n7, N.n9⟩
  unfold lX
  linarith

theorem prime_sum_facts_along_family {eps : ℝ} (Fm : FamP eps) (K : Consts) (hK : K.Nonneg) (C31 Ce Cm : ℝ) (C : ℝ)
    (hC : 0 ≤ C) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i))
    (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      PrimeSumNumericFacts (Fm.D x i) (Fm.L x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    simpa only [Fm.L_eps] using (Fm.L 0 i).sc.eps_pos
  obtain ⟨x1, _, H1⟩ := hA (eps / 48) (by positivity)
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (Nu.prime_sum_facts_eventually eps K hK (40 * C) (by positivity))
  refine ⟨max (Fm.x1 + 1) (max x1 x2), fun x hx i => ?_⟩
  have h0 : Fm.x1 < x := by have := le_trans (le_max_left _ _) hx; linarith
  have h1 : x ≥ x1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have h2 : x ≥ x2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨_, _, _, _, a5, _, _, _, _, _, _, aSz⟩ := H1 x h1 i
  exact prime_sum_facts_of_scaled hC
    (H2 x h2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i h0) (Fm.L_eps x i) aSz.1 (Fm.params x h0 i) a5)

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeRpowNegLevelLe\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SummableAndTsumLeTwoMulDivOfLeDivPow\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.SecondConstantNonneg\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.DfcHigh\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

structure NumT (D : D7) (L : SizeData₂ D) (C : ℝ) : Prop where
  t9 : (L.sc.X'' D.R.n * thS L + 2) * (Real.log (2 * L.sc.X'' D.R.n) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) ≤
    L.sc.a * L.sc.x ^ (-16 : ℝ)
  t1 : c1 L C * (L.sc.X'' D.R.n + 2) ≤ L.sc.b * L.sc.x ^ (-100 : ℝ)
  t1' : cfl D L.sc C * (L.sc.X'' D.R.n + 2) ≤ L.sc.b * L.sc.x ^ (-100 : ℝ)

theorem inWin_of_boxT {K : Consts} {a b : HH D → ℤ} (ha : a ∈ box D (winA D L.sc)) (hb : b ∈ box D (winB D K L.sc)) :
    InWin L a b := by
  classical
  intro t ht
  unfold box at ha hb
  have h1 := Fintype.mem_piFinset.1 ha t
  have h2 := Fintype.mem_piFinset.1 hb t
  rw [if_pos ht] at h1 h2
  unfold winA at h1
  unfold winB at h2
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.1 h1
  obtain ⟨h2a, _⟩ := Finset.mem_Icc.1 h2
  exact ⟨Int.ceil_le.1 h1a, Int.le_floor.1 h1b, Int.ceil_le.1 h2a⟩

theorem sum_le_count (S : Finset ℕ) (y c : ℝ) (hy : 0 ≤ y) (hc : 0 ≤ c) (f : ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ y) (hf : ∀ p ∈ S, f p ≤ c) : ∑ p ∈ S, f p ≤ c * (y + 2) := by
  have hsub : S ⊆ prB (y + 1) := fun p hp => mem_prB.2 ⟨(hS p hp).1, by have := (hS p hp).2; linarith⟩
  have h1 : (S.card : ℝ) ≤ y + 2 := by
    have h2 : (S.card : ℝ) ≤ ((prB (y + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have h3 := card_prB_le (y + 1) (by linarith)
    linarith
  have h4 := Finset.sum_le_card_nsmul S f c hf
  rw [nsmul_eq_mul] at h4
  exact h4.trans (by rw [mul_comm c]; exact mul_le_mul_of_nonneg_right h1 hc)

theorem third_estimate_of_numeric_facts (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (C : ℝ) (hC : 0 ≤ C) (N : NumT D L C) :
    WeightedPrimeSumBound D L X K C := by
  classical
  have hX1 : 1 ≤ L.sc.X'' D.R.n := (one_le_X' L.sc).trans (X'_le_X'' L.sc D.R.n (n_pos D))
  have hX0 : 0 < L.sc.X'' D.R.n := one_pos.trans_le hX1
  refine ⟨fun a ha b hb S hS => ?_, fun S hS => ⟨?_, ?_⟩⟩
  · have h := inWin_of_boxT ha hb
    have hSc0 : 0 ≤ L.Sc := by linarith only [(Sc_facts P).1]
    obtain ⟨hth0, hth1⟩ := thS_bounds P
    have hm : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
    have hM : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.host.TT.card : ℝ) := mul_nonneg hm hN
    have ht0 := (thW_bounds D L.sc).1
    have hθ0 := ht0.le.trans hth0
    have hw := sc_w''_pos L.sc D.R.n (n_pos D)
    have hl2 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) := Real.log_nonneg (by linarith only [hX1])
    have hcoef : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) *
        ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc)) :=
      mul_nonneg hl2 (mul_nonneg hM (add_nonneg (mul_nonneg ht0.le hw.le) hSc0))
    set R9 : Finset ℕ := Finset.Ioc ⌊L.sc.X'' D.R.n⌋₊ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ with hR9
    have hdd : ∀ p ∈ S, 0 ≤ (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ∧
        (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤ (D.R.m : ℝ) * ((D.host.TT.card : ℝ) *
        (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0)) := by
      intro p hp
      have hpX := (hS p hp).2.2
      constructor
      · exact Finset.sum_nonneg (fun j hj => Finset.sum_nonneg (fun s hs => (ask_bounds P X h p (hS p hp).1 j hj s hs).1))
      · have hj : ∀ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s ≤ (D.host.TT.card : ℝ) *
            (if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0) := by
          intro j hjl
          rw [← nsmul_eq_mul]
          apply Finset.sum_le_card_nsmul
          intro s hs
          exact ask_high P X h p hpX j hjl s hs
        have hs := Finset.sum_le_card_nsmul _ _ _ hj
        rw [lifts_card, nsmul_eq_mul] at hs
        exact hs
    have hpt : ∀ p ∈ S, Real.log p * (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤
        (if p ∈ R9 then (1 : ℝ) else 0) * (Real.log (2 * L.sc.X'' D.R.n) *
          ((D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc))) := by
      intro p hp
      have hpX := (hS p hp).2.2
      obtain ⟨hd0, hd⟩ := hdd p hp
      have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
      by_cases hlt : (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L)
      · rw [if_pos hlt] at hd
        have hmem : p ∈ R9 := by
          rw [hR9]
          refine Finset.mem_Ioc.2 ⟨(Nat.floor_lt hX0.le).2 hpX, ?_⟩
          exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
        rw [if_pos hmem, one_mul]
        have h1 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤
            (D.R.m : ℝ) * (D.host.TT.card : ℝ) * (thW D L.sc * L.sc.w'' D.R.n + L.Sc) := by
          simpa only [mul_assoc] using hd
        have h2 : Real.log p ≤ Real.log (2 * L.sc.X'' D.R.n) := by
          apply Real.log_le_log (hX0.trans hpX)
          rw [mul_comm (2 : ℝ)]
          exact hlt.le.trans (mul_le_mul_of_nonneg_left (by linarith only [hth1]) hX0.le)
        exact mul_le_mul h2 h1 hd0 hl2
      · rw [if_neg hlt] at hd
        have h1 : (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) = 0 :=
          le_antisymm (by simpa only [mul_zero] using hd) hd0
        rw [h1, mul_zero]
        split_ifs
        · rw [one_mul]; exact hcoef
        · rw [zero_mul]
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.sum_mul]
    have b9 : ∑ p ∈ S, (if p ∈ R9 then (1 : ℝ) else 0) ≤ L.sc.X'' D.R.n * thS L + 2 := by
      refine le_trans (sum_ite_mem_le (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)) ?_
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hR9, Nat.card_Ioc]
      have hle : ⌊L.sc.X'' D.R.n⌋₊ ≤ ⌈L.sc.X'' D.R.n * (1 + thS L)⌉₊ :=
        le_trans (Nat.floor_le_floor (le_mul_of_one_le_right hX0.le (le_add_of_nonneg_right hθ0)))
          (Nat.floor_le_ceil _)
      rw [Nat.cast_sub hle]
      have h1 := Nat.ceil_lt_add_one (mul_nonneg hX0.le (add_nonneg zero_le_one hθ0))
      have h2 := Nat.lt_floor_add_one (L.sc.X'' D.R.n)
      linarith only [h1, h2]
    refine le_trans (mul_le_mul_of_nonneg_right b9 hcoef) ?_
    have e1 := mul_le_mul_of_nonneg_left N.t9 hM
    linarith only [e1]
  · refine le_trans (sum_le_count S (L.sc.X'' D.R.n) (c1 L C) hX0.le (first_constant_nonneg L C hC) _ hS (fun p hp => ?_)) N.t1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).1.one_lt
    have hl : 0 < Real.log p := Real.log_pos hp1
    apply le_of_eq
    unfold c1 Real.logb
    field_simp
  · exact le_trans (sum_le_count S (L.sc.X'' D.R.n) (cfl D L.sc C) hX0.le (cfl_nonneg D L.sc C hC) _ hS
      (fun p hp => (fl_bounds D L.sc C hC p (hS p hp).1).2)) N.t1'

namespace Nu

theorem numeric_ninth_arith (Xpp θ lg w a x S Y X' z : ℝ) (hXw : Xpp * w = a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ 2 * x) (hlgY : lg ≤ Y) (hw1 : 1 ≤ w) (hx : 0 < x)
    (hq1 : 8 * x * θ ^ 2 ≤ z) (hq2 : 16 * x * θ ≤ z * Xpp) (hS0 : 0 ≤ S) (hSY : S ≤ Y) (hY : 10 ≤ Y) (hX1 : 1 ≤ Xpp)
    (hXY : Xpp ≤ X' * Y) (hX'0 : 0 ≤ X') (e7 : Y ^ 7 * X' ≤ a * z) :
    (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) ≤ a * z := by
  have hw0 : 0 < w := one_pos.trans_le hw1
  have hY0 : 0 ≤ Y := hlg0.trans hlgY
  have hXp0 : 0 ≤ Xpp := zero_le_one.trans hX1
  have ha0 : 0 ≤ a := by rw [← hXw]; exact mul_nonneg hXp0 hw0.le
  have e : (Xpp * (θ + 3 * S / w) + 2) * (lg * (θ * w + S)) =
      lg * ((Xpp * w) * θ ^ 2) + lg * (2 * θ * w) +
        lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) := by
    field_simp
    ring
  rw [e, hXw]
  have T1a : lg * (a * θ ^ 2) ≤ a * z / 4 := by
    calc lg * (a * θ ^ 2) ≤ (2 * x) * (a * θ ^ 2) := mul_le_mul_of_nonneg_right hlg (by positivity)
      _ = a * (8 * x * θ ^ 2) / 4 := by ring
      _ ≤ a * z / 4 := by
          have := mul_le_mul_of_nonneg_left hq1 ha0
          linarith
  have T1b : lg * (2 * θ * w) ≤ a * z / 4 := by
    calc lg * (2 * θ * w) ≤ (2 * x) * (2 * θ * w) := mul_le_mul_of_nonneg_right hlg (by positivity)
      _ = (16 * x * θ) * w / 4 := by ring
      _ ≤ (z * Xpp) * w / 4 := by
          have := mul_le_mul_of_nonneg_right hq2 hw0.le
          linarith
      _ = a * z / 4 := by rw [← hXw]; ring
  have hXw' : Xpp / w ≤ Xpp := div_le_self hXp0 hw1
  have hXw0 : 0 ≤ Xpp / w := by positivity
  have hYY : Y ≤ Y ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right hY0 (by linarith only [hY])
  have a0 : Xpp * θ ≤ Xpp := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hθ1 hXp0
  have a1 : (Xpp * θ + 2) * S ≤ (3 * Xpp) * Y := mul_le_mul (by linarith) hSY hS0 (by linarith)
  have a2 : 3 * S * Xpp * θ ≤ 3 * Y * Xpp := by
    have h1 : 3 * S * Xpp ≤ 3 * Y * Xpp := by gcongr
    have h2 : 3 * S * Xpp * θ ≤ 3 * S * Xpp * 1 := mul_le_mul_of_nonneg_left hθ1 (by positivity)
    linarith
  have a3 : 3 * S ^ 2 * (Xpp / w) ≤ 3 * Y ^ 2 * Xpp := by gcongr
  have a4 : Y * Xpp ≤ Y ^ 2 * Xpp := mul_le_mul_of_nonneg_right hYY hXp0
  have t2 : (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) ≤ 9 * Y ^ 2 * Xpp := by linarith
  have t20 : 0 ≤ (Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w) := by positivity
  have T2 : lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ a * z / 80 := by
    have h3 : (1000 : ℝ) ≤ Y ^ 3 := by
      calc (1000 : ℝ) = 10 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY 3
    have h4 : 0 ≤ Y ^ 4 * X' := by positivity
    have h5 : 720 * (Y ^ 4 * X') ≤ Y ^ 7 * X' := by
      calc 720 * (Y ^ 4 * X') ≤ Y ^ 3 * (Y ^ 4 * X') := mul_le_mul_of_nonneg_right (by linarith) h4
        _ = Y ^ 7 * X' := by ring
    calc lg * ((Xpp * θ + 2) * S + 3 * S * Xpp * θ + 3 * S ^ 2 * (Xpp / w)) ≤ Y * (9 * Y ^ 2 * Xpp) :=
          mul_le_mul hlgY t2 t20 hY0
      _ ≤ Y * (9 * Y ^ 2 * (X' * Y)) := by gcongr
      _ = 9 * (Y ^ 4 * X') := by ring
      _ ≤ a * z / 80 := by linarith
  have haz : 0 ≤ a * z := le_trans (by positivity) e7
  linarith

theorem two_mul_le_sq (x : ℝ) (h : 16 ≤ x) : 2 * x ≤ x ^ 2 := by
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (by linarith only [h]) (by linarith only [h])

theorem sixteen_le (X' x n : ℝ) (hX : 1 ≤ X') (hx : 16 ≤ x) (hn : 1 ≤ n) : 16 ≤ X' * (x * n) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  calc 16 ≤ x := hx
    _ ≤ x * n := le_mul_of_one_le_right hx0 hn
    _ ≤ X' * (x * n) := le_mul_of_one_le_left (mul_nonneg hx0 (zero_le_one.trans hn)) hX

theorem theta_power_bounds (x k θ Xpp : ℝ) (hx : 16 ≤ x) (hk4 : x ^ 4 ≤ k) (hθ : θ = 1 / (k * x ^ 13)) (hX : 16 ≤ Xpp) :
    0 ≤ θ ∧ 8 * x * θ ^ 2 ≤ (x ^ 16)⁻¹ ∧ 16 * x * θ ≤ (x ^ 16)⁻¹ * Xpp := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk4
  have hkx : x ^ 17 ≤ k * x ^ 13 := by
    calc x ^ 17 = x ^ 4 * x ^ 13 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk4 (pow_pos hx0 13).le
  have hθle : θ ≤ (x ^ 17)⁻¹ := by
    rw [hθ, one_div]
    exact inv_anti₀ (by positivity) hkx
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hx16p : 0 < x ^ 16 := by positivity
  have hx17p : 0 < x ^ 17 := by positivity
  refine ⟨hθ0, ?_, ?_⟩
  · have h1 : θ ^ 2 ≤ ((x ^ 17)⁻¹) ^ 2 := pow_le_pow_left₀ hθ0 hθle 2
    have h2 : 8 * x * ((x ^ 17)⁻¹) ^ 2 ≤ (x ^ 16)⁻¹ := by
      have e1 : 8 * x * ((x ^ 17)⁻¹) ^ 2 = (8 * (x ^ 17)⁻¹) * (x ^ 16)⁻¹ := by field_simp
      rw [e1]
      have h3 : (8 : ℝ) ≤ x ^ 17 := le_trans (by linarith) (le_self_pow₀ hx1 (by norm_num))
      have h4 : 8 * (x ^ 17)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hx17p]; exact h3
      calc (8 * (x ^ 17)⁻¹) * (x ^ 16)⁻¹ ≤ 1 * (x ^ 16)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = _ := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
  · have h1 : 16 * x * θ ≤ 16 * x * (x ^ 17)⁻¹ := mul_le_mul_of_nonneg_left hθle (by positivity)
    have h2 : 16 * x * (x ^ 17)⁻¹ = (x ^ 16)⁻¹ * 16 := by field_simp
    calc 16 * x * θ ≤ (x ^ 16)⁻¹ * 16 := by rw [← h2]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)


theorem numT_ev (eps : ℝ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → NumT D L C := by
  by_cases he : 0 < eps ∧ eps < 1 / 52
  swap
  · refine Filter.Eventually.of_forall fun x D L _ h2 => ?_
    exact absurd ⟨h2 ▸ L.sc.eps_pos, h2 ▸ L.sc.eps_lt⟩ he
  obtain ⟨he0, he1⟩ := he
  have hτ : 0 < 23 * eps / 48 := by positivity
  have F1 := ev_log 14 (23 * eps / 48) hτ
  have F2 := ev_const C (23 * eps / 48) hτ
  have F3 := ev_const 10 (23 * eps / 48) hτ
  have F4 := ev_log 1 eps he0
  have F5 := ev_pow 3 eps 1 (by linarith)
  have F6 := ev_pow 14 (23 * eps / 48) eps (by linarith)
  have F7 := ev_pow 4 (eps / 3) eps (by linarith)
  have F8 := ev_log 5 1 one_pos
  have F9 := ev_log 400 eps he0
  filter_upwards [F1, F2, F3, F4, F5, F6, F7, F8, F9, eventually_ge_atTop 16]
    with x f1 f2 f3 f4 f5 f6 f7 f8 f9 hx16 D L hx heps hS P
  subst hx
  subst heps
  have hx0 := sc_x_pos L.sc
  have hx1 := L.sc.one_lt_alt
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hk0 : (0 : ℝ) < (D.R.k : ℝ) := one_pos.trans_le hk1
  obtain ⟨_, hNmSc, hSc100⟩ := Nm_le_Sc P
  obtain ⟨hSN, -, hSK, -, -, -, -, -, -, -, -, -, -, hSEta, -, -, hSDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hSN
  unfold Formalism.MainNotions.SizeK Formalism.MainNotions.szTh at hSK
  unfold Formalism.MainNotions.SizeEta at hSEta
  unfold Formalism.MainNotions.SizeDel at hSDel
  rw [Real.rpow_one] at f5 f8
  have mono : ∀ u v : ℝ, u ≤ v → L.sc.x ^ u ≤ L.sc.x ^ v := fun u v h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have nat4 : L.sc.x ^ (4 : ℝ) = L.sc.x ^ 4 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat3 : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have nat6 : L.sc.x ^ (6 : ℝ) = L.sc.x ^ 6 := by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have natA2 : L.sc.x ^ (Scale.A / 2) = L.sc.x ^ 13 := by
    unfold Scale.A; rw [show (26 / 2 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    rw [← nat3]; exact le_trans hSN.2 (mono _ _ (by linarith only [he1]))
  have hn2 : L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    rw [← nat2]; exact le_trans (mono _ _ (by linarith only [he0])) hSN.1
  have hk4 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by
    rw [← nat4]; exact le_trans (mono _ _ (by linarith only [he0])) hSK.1
  rw [nat6] at hk6
  have hn0 : (0 : ℝ) < (D.R.n : ℝ) := lt_of_lt_of_le (by positivity) hn2
  have hxe1 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le he0.le
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hb0 : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha0 : 0 < L.sc.a := by rw [ha]; exact mul_pos hx0 hb0
  have hXd : L.sc.X' = Real.exp (L.sc.x ^ (L.sc.eps / 3)) := rfl
  have hX0 : 0 < L.sc.X' := by rw [hXd]; exact Real.exp_pos _
  have hX1 : 1 ≤ L.sc.X' := by rw [hXd]; exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hXpp : L.sc.X'' D.R.n = L.sc.X' * (L.sc.x * (D.R.n : ℝ)) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    rw [div_div, div_div_cancel₀ ha0.ne']
  have hlogX : Real.log L.sc.X' = L.sc.x ^ (L.sc.eps / 3) := by rw [hXd, Real.log_exp]

  have hY10 : 10 ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := f3
  have pY : ∀ q : ℝ, ∀ M : ℕ, q ≤ L.sc.x ^ M → M ≤ 14 → q ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    intro q M hq hM
    refine le_trans hq ?_
    rw [← Real.rpow_natCast]
    apply xpow_le_exp _ _ _ hx0
    have : (M : ℝ) ≤ 14 := by exact_mod_cast hM
    exact le_trans (mul_le_mul_of_nonneg_right this hlx0) f1
  have hT4 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (23 * L.sc.eps / 48) :=
    mono _ _ (by linarith only [he0])
  have e_eta : L.etaSz ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc L.etaSz ≤ Real.exp (Real.log L.etaSz) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4)) := Real.exp_le_exp.2 hSEta.2.2.1
      _ ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := Real.exp_le_exp.2 hT4
  have e_Del : (D.s.Del : ℝ) ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
    calc (D.s.Del : ℝ) ≤ Real.exp (Real.log (D.s.Del : ℝ)) := Real.le_exp_log _
      _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := Real.exp_le_exp.2 hSDel.2.2.1
      _ ≤ _ := Real.exp_le_exp.2 (div_le_div_of_nonneg_right hT4 (by norm_num))
  have hDel0 : (0 : ℝ) ≤ (D.s.Del : ℝ) :=
    le_trans (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) hSDel.1
  have h7 : L.sc.x * L.sc.x ^ 6 ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := by
    have : L.sc.x * L.sc.x ^ 6 = L.sc.x ^ ((7 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; ring
    rw [this]
    apply xpow_le_exp _ _ _ hx0
    push_cast
    linarith only [f1]
  have hSc0 : 0 ≤ L.Sc := by linarith only [hSc100]
  have hcG0 : 0 ≤ cG L := mul_nonneg (by norm_num) hSc0
  have e_c : cG L ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
    calc cG L = (16 * (D.R.k : ℝ)) * (D.s.Del : ℝ) := by unfold cG; rw [L.Sc_eq]; ring
      _ ≤ (L.sc.x * L.sc.x ^ 6) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) :=
          mul_le_mul (mul_le_mul hx16 hk6 hk0.le hx0.le) e_Del hDel0 (by positivity)
      _ ≤ Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) * Real.exp ((L.sc.x ^ (23 * L.sc.eps / 48)) / 2) := mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      _ = (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by rw [← Real.exp_add]; congr 1; ring
  have hScY : L.Sc ≤ Real.exp (L.sc.x ^ (23 * L.sc.eps / 48)) :=
    le_trans (show L.Sc ≤ cG L by unfold cG; linarith only [hSc0]) e_c
  have e_Nm : Nm D ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := hNmSc.trans hScY
  have hNm0 : 0 ≤ Nm D := by unfold Nm; exact Nat.cast_nonneg _
  have e_xn : L.sc.x * (D.R.n : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 4 (le_trans (mul_le_mul_of_nonneg_left hn3 hx0.le) (le_of_eq (by ring))) (by norm_num)
  have e_f : (D.R.f : ℝ) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by unfold Ranks.f; push_cast; ring
    rw [hf]
    exact le_trans (mul_le_mul_of_nonneg_right (by linarith only [hx16]) hn0.le) e_xn
  have hla : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, hb, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hxY : L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := pY _ 1 (by rw [pow_one]) (by norm_num)
  have e_la : Real.log L.sc.a ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    rw [hla]; linarith only [f4, f5, hxY, hxe1]
  have hla0 : 0 ≤ Real.log L.sc.a := by
    rw [hla]; exact add_nonneg hlx0 (Real.rpow_nonneg hx0.le _)
  have e_la2 : Real.log (2 * L.sc.a) ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) := by
    rw [Real.log_mul (by norm_num) ha0.ne', hla]
    linarith only [Real.log_two_lt_d9, f4, f5, hxY, hxe1]
  have hla20 : 0 ≤ Real.log (2 * L.sc.a) := Real.log_nonneg (by linarith only [sc_one_lt_a L.sc])
  have hz100 : 0 < L.sc.x ^ (-100 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have e7 : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 7 * L.sc.X' ≤ L.sc.b * L.sc.x ^ (-100 : ℝ) := by
    have hxe : L.sc.x ^ (-100 : ℝ) = Real.exp (-100 * Real.log L.sc.x) := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; ring
    rw [hb, hXd, hxe, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    linarith only [f6, f7, f9]
  refine ⟨?_, ?_, ?_⟩
  ·
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.a :=
      (mul_comm _ _).trans (X''_eq L.sc D.R.n (n_pos D))
    have hq1 : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ 13 := one_le_mul_of_one_le_of_one_le hk1 (one_le_pow₀ hx1.le)
    have hθ : thW D L.sc = 1 / ((D.R.k : ℝ) * L.sc.x ^ 13) := by unfold thW; rw [natA2]
    have hlg : Real.log (2 * L.sc.X'' D.R.n) ≤ 2 * L.sc.x := by
      rw [hXpp, show 2 * (L.sc.X' * (L.sc.x * (D.R.n : ℝ))) = L.sc.X' * (2 * (L.sc.x * (D.R.n : ℝ))) by ring,
        Real.log_mul hX0.ne' (by positivity), hlogX]
      have h1 : 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        have h0 := mul_le_mul_of_nonneg_left hn3 hx0.le
        calc 2 * (L.sc.x * (D.R.n : ℝ)) ≤ L.sc.x * (L.sc.x * L.sc.x ^ 3) :=
              mul_le_mul (by linarith only [hx16]) h0 (by positivity) hx0.le
          _ = L.sc.x ^ 5 := by ring
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow hx0] at h2
      push_cast at h2
      have h3 : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x := by
        have := mono (L.sc.eps / 3) 1 (by linarith only [he1])
        rwa [Real.rpow_one] at this
      linarith only [h2, h3, f8]
    have hn1 : (1 : ℝ) ≤ (D.R.n : ℝ) := le_trans (one_le_pow₀ hx1.le) hn2
    have hXpp1 : 1 ≤ L.sc.X'' D.R.n := by
      rw [hXpp]
      exact one_le_mul_of_one_le_of_one_le hX1 (one_le_mul_of_one_le_of_one_le hx1.le hn1)
    have hlg0 : 0 ≤ Real.log (2 * L.sc.X'' D.R.n) :=
      Real.log_nonneg (by linarith only [hXpp1])
    have h2xY : 2 * L.sc.x ≤ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) :=
      pY _ 2 (two_mul_le_sq _ hx16) (by norm_num)
    have hz16 : L.sc.x ^ (-16 : ℝ) = (L.sc.x ^ 16)⁻¹ := by
      rw [Real.rpow_neg hx0.le, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hXpp16 : 16 ≤ L.sc.X'' D.R.n := by
      rw [hXpp]; exact sixteen_le _ _ _ hX1 hx16 hn1
    obtain ⟨hθ0, hr1, hr2⟩ := theta_power_bounds L.sc.x (D.R.k : ℝ) (thW D L.sc) (L.sc.X'' D.R.n) hx16 hk4 hθ hXpp16
    rw [← hz16] at hr1 hr2
    have e7a : (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) ^ 7 * L.sc.X' ≤ L.sc.a * L.sc.x ^ (-16 : ℝ) := by
      refine le_trans e7 ?_
      have h1 : L.sc.b ≤ L.sc.a := by rw [ha]; exact le_mul_of_one_le_left hb0.le hx1.le
      exact mul_le_mul h1 (mono _ _ (by norm_num)) hz100.le ha0.le
    have hw1 : 1 ≤ L.sc.w'' D.R.n := by linarith only [hSc100, (Sc_facts P).2]
    unfold thS
    exact numeric_ninth_arith _ _ _ _ L.sc.a L.sc.x L.Sc (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) L.sc.X' _ hXw
      hθ0 (by rw [hθ, div_le_one (one_pos.trans_le hq1)]; exact hq1) hlg0 hlg (le_trans hlg h2xY)
      hw1 hx0 hr1 hr2 hSc0 hScY hY10 hXpp1
      (by rw [hXpp]; exact mul_le_mul_of_nonneg_left e_xn hX0.le) hX0.le e7a
  ·
    rw [hXpp]
    unfold c1
    exact first_bound_arith C (cG L) L.etaSz _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC hcG0 L.etaSz_pos.le hla20 (by positivity) f2 e_c e_eta e_la2 e_xn
      hX1 hY10 e7
  ·
    rw [hXpp]
    unfold cfl
    exact n1'_arith C _ (Nm D) _ _ _ (Real.exp (L.sc.x ^ (23 * L.sc.eps / 48))) _ hC (Nat.cast_nonneg _) hNm0 hla0 (by positivity) f2 e_f e_Nm e_la e_xn
      hX1 hY10 e7

end Nu

theorem third_estimate_along_family {eps : ℝ} (Fm : FamP eps) (K : Consts) (_hK : K.Nonneg) (C31 Ce Cm : ℝ) (C : ℝ)
    (hC : 0 ≤ C) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i))
    (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C := by
  obtain ⟨x1, _, H1⟩ := hA 1 one_pos
  obtain ⟨x2, H2⟩ := Filter.eventually_atTop.1 (Nu.numT_ev eps C hC)
  refine ⟨max (Fm.x1 + 1) (max x1 x2), fun x hx i => ?_⟩
  have h0 : Fm.x1 < x := by have := le_trans (le_max_left _ _) hx; linarith
  have h1 : x ≥ x1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have h2 : x ≥ x2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, aSz⟩ := H1 x h1 i
  exact third_estimate_of_numeric_facts (Fm.params x h0 i) (X x i) K C hC
    (H2 x h2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i h0) (Fm.L_eps x i) aSz.1 (Fm.params x h0 i))

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts =====

-- ===== clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums =====
-- clump-header: {"m": "Formalism.SharpRestriction.GrowthBounds.LogarithmicSums", "h": "module\n\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.GainBoundAllAddOneOfGainBoundAllRequired\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NotSingularOfCentral\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.MeanNum\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.LatticeChainSuccOfPartial\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSumNumericFacts\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.ThirdEstimateOfNumericFacts\npublic import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarFam\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def RestStar {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C ≥ C0,
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        StarAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

theorem bo_nonneg (s : Scale) (y : ℝ) : 0 ≤ s.b ^ y := Real.rpow_nonneg (Real.exp_pos s.L).le y

private theorem eventually_adm_of_admFam {eps : ℝ} (Fm : FamP eps) {K : Consts}
    {X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)} {Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)}
    {C31 Ce Cm : ℝ} (hA : AdmFam Fm K X Y C31 Ce Cm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x ∧
      ∀ i : Fm.Ix x, admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, 1⟩ := by
  obtain ⟨x0, -, h⟩ := hA 1 one_pos
  refine ⟨max x0 (Fm.x1 + 1), fun x hx => ⟨?_, h x (le_trans (le_max_left _ _) hx)⟩⟩
  linarith [le_trans (le_max_right _ _) hx]

theorem rest0 {eps : ℝ} (Fm : FamP eps) : FamilyAskBounds Fm := by
  intro K _ C31 Ce Cm _ _ _ X Y hA
  obtain ⟨x0, h⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSz⟩ := (h x hx).2 i
  exact As.asksAll_of (X x i) hSz.2.2

theorem remainingCountingStatement_of_restStar {eps : ℝ} (Fm : FamP eps) (hS : RestStar Fm) : RemainingCountingStatement Fm := by
  intro K hK C31 Ce Cm hC31 hCe _
  obtain ⟨C0, hC0, hS'⟩ := hS K hK C31 Ce Cm hC31
  obtain ⟨C1, hC01, h3, hd1, hd2⟩ : ∃ C1 : ℝ, C0 ≤ C1 ∧ 3 ≤ C1 ∧ 2 * K.dl1 + (Ce + 1) ≤ C1 ∧
      4 * K.dl2 ≤ C1 :=
    ⟨max C0 (max 3 (max (2 * K.dl1 + (Ce + 1)) (4 * K.dl2))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _),
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)⟩
  refine ⟨C1 + 1, by linarith, fun X Y hA => ?_⟩
  obtain ⟨x1, h1⟩ := hS' C1 hC01 X Y hA
  obtain ⟨x2, h2⟩ := eventually_adm_of_admFam Fm hA
  refine ⟨max x1 x2, fun x hx i => ?_⟩
  obtain ⟨hxp, hadm⟩ := h2 x (le_trans (le_max_right _ _) hx)
  obtain ⟨-, -, -, -, -, -, -, -, a9, -, -, aSz⟩ := hadm i
  have hN : GainBoundConstants K (Ce + 1) C1 ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) :=
    ⟨h3, hd1, hd2, bo_nonneg _ _⟩
  have hP := gain_bound_all_of_star (Fm.params x hxp i) (X x i) K hK Ce C1 _ hCe hN a9
    (h1 x (le_trans (le_max_left _ _) hx) i)
  have hNc : Nm (Fm.D x i) ≤ cG (Fm.L x i) :=
    (basics (Fm.params x hxp i)).2.1.trans (St.base (Fm.params x hxp i)).2.2.2.2
  exact As.gainBoundAll_add_one_of_gainBoundAllRequired (X x i) K hK.1 C1 _ (As.asksAll_of (X x i) aSz.2.2) hNc hP

theorem rest2 {eps : ℝ} (Fm : FamP eps) : FamilyFourthBound Fm := by
  intro K hK C31 Ce Cm _ _ hCm X Y hA
  obtain ⟨x0, h⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  exact ⟨x0, fun x hx i => (h x hx i).1⟩

theorem restW {eps : ℝ} (Fm : FamP eps) : RestW Fm := by
  intro K hK C31 Ce Cm _ _ hCm X Y hA
  obtain ⟨x0, h⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  exact ⟨x0, fun x hx i => weight_condition_of_mean_excess (X x i) K (h x hx i).2⟩

theorem rest3 {eps : ℝ} (Fm : FamP eps) : FamilyFifthBound Fm := by
  intro K hK C31 Ce Cm _ _ hCm C hC X Y hA
  obtain ⟨x1, h1⟩ := eventually_adm_of_admFam Fm hA
  obtain ⟨x2, h2⟩ := second_estimate_and_mean_along_family Fm K hK C31 Ce Cm hCm X Y hA
  obtain ⟨x3, h3⟩ := G5.prime_sum_facts_along_family Fm K hK C31 Ce Cm C hC X Y hA
  refine ⟨max x1 (max x2 x3), fun x hx i hG => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hxp, hadm⟩ := h1 x hx1
  obtain ⟨-, a2, a3, a4, -⟩ := hadm i
  exact G5.latticeChain_succ_of_partial (X x i) K hK (Fm.params x hxp i) C _ hC (bo_nonneg _ _) hG (h2 x hx2 i).2.1
    a2 a3 a4 (h3 x hx3 i)

theorem restT {eps : ℝ} (Fm : FamP eps) : RestT Fm := by
  intro K hK C31 Ce Cm _ _ _ C hC X Y hA
  exact G5.third_estimate_along_family Fm K hK C31 Ce Cm C hC X Y hA

theorem restStar {eps : ℝ} (Fm : FamP eps) : RestStar Fm := by
  exact St.star_fam Fm

theorem stmtEF {eps : ℝ} (Fm : FamP eps) : FamilyClosedForm Fm :=
  stmtEF_of Fm (rest0 Fm) (remainingCountingStatement_of_restStar Fm (restStar Fm)) (rest2 Fm) (restW Fm) (rest3 Fm) (restT Fm)

theorem stmtF {eps : ℝ} (Fm : FamP eps) : KudlaFamilyStatement Fm :=
  stmtF_of_stmtEF Fm (stmtEF Fm)

end Formalism.MainNotions.AuxBlock8.Pf

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.GrowthBounds.LogarithmicSums =====
