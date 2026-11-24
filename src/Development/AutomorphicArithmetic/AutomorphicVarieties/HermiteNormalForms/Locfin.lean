module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.locfin :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N → ∀ B : ℝ,
    ∃ S : Set (Lat L N), S.Finite ∧ ∀ᶠ k in nhds h, ∀ y ∉ S, B < q k y := by
  intro L _ _ N h hh B
  obtain ⟨c, hc, hev⟩ := lowbd L N h hh
  obtain ⟨R, hR⟩ := exists_nat_gt (max (B / c) 1)
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRB : B / c < R := lt_of_le_of_lt (le_max_left _ _) hR
  set T := {a : 𝓞 L | ∀ w : InfinitePlace L, ‖embO w a‖ ≤ (R : ℝ)} with hT
  refine ⟨Set.pi Set.univ (fun _ => T), Set.Finite.pi (fun _ => (cntconj L R).1), ?_⟩
  filter_upwards [hev] with k hk
  intro y hy
  have hy' : ∃ a w, (R : ℝ) < ‖embO w (y a)‖ := by
    by_contra hne
    push_neg at hne
    exact hy (fun a _ w => hne a w)
  obtain ⟨a, w, hlt⟩ := hy'
  have hle : ‖embO w (y a)‖ ≤ ‖toR y‖ :=
    (norm_le_pi_norm (toR y w) a).trans (norm_le_pi_norm (toR y) w)
  have hzR : (R : ℝ) < ‖toR y‖ := hlt.trans_le hle
  have hz1 : (1 : ℝ) ≤ ‖toR y‖ := hR1.le.trans hzR.le
  have hsq : ‖toR y‖ ≤ ‖toR y‖ ^ 2 := by nlinarith
  have hB : B < c * ‖toR y‖ := by
    rw [div_lt_iff₀ hc] at hRB
    nlinarith
  exact lt_of_lt_of_le (hB.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)) (hk (toR y))
