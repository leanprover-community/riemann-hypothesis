module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.QuotientOutRightInvariant
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcN.F2.LocOpPf

theorem finsum_quot_le {H : Type} [Group H] {S T : Subgroup H} (hST : S ≤ T) (u : H → ℂ)
    (hu : ∀ x, ∀ t ∈ T, u (x * t) = u x) (hrel : S.relIndex T ≠ 0)
    (hfin : (Function.support fun q : H ⧸ S => u q.out).Finite) :
    ∑ᶠ q : H ⧸ S, u q.out = (S.relIndex T : ℂ) * ∑ᶠ q : H ⧸ T, u q.out :=
  _root_.UpperTheory.Reformulated.B.P6.r20a.PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le hST u hu hrel hfin

theorem hinteq {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ) (hSK : S ≤ K) (hSu : S ≤ rStab u)
    (hrel : S.relIndex K ≠ 0) (hfin : (Function.support fun q : H ⧸ S => u q.out).Finite) :
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  have hS0 : S ≤ rStab u ⊓ K := le_inf hSu hSK
  have hmul := Subgroup.relIndex_mul_relIndex S (rStab u ⊓ K) K hS0 inf_le_right
  have h1 : S.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact hrel hmul.symm
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h; rw [h, mul_zero] at hmul; exact hrel hmul.symm
  have hu : ∀ x, ∀ t ∈ rStab u ⊓ K, u (x * t) = u x := fun x t ht => ht.1 x
  rw [finsum_quot_le hS0 u hu h1 hfin, hint, ← hmul]
  push_cast
  field_simp

end PositivityTheory.Rg.BcN.F2.LocOpPf
