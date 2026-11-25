module

public import Formalism.IncomingBounds.StatementThmP
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Formalism.IncomingBounds.IncomingBound
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdIccMulFactorial
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.IncomingBounds.FlowDegreeBounds.Cayley, Formalism.IncomingBounds.FlowDegreeBounds.LemmaF, Formalism.IncomingBounds.WeightIdentities

-- ===== clump member: Formalism.IncomingBounds.FlowDegreeBounds.Cayley =====
-- clump-header: {"m": "Formalism.IncomingBounds.FlowDegreeBounds.Cayley", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdIccMulFactorial\npublic import Formalism.IncomingBounds.StatementThmP\npublic import Mathlib.Algebra.MvPolynomial.PDeriv\npublic import Mathlib.LinearAlgebra.Matrix.Adjugate\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds.Cay

open MvPolynomial Matrix Formalism.IncomingBounds

variable {K : Type} [Field K] [CharZero K]

def dm {σ : Type} (m : σ →₀ ℕ) (Q : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ a ∈ Q.support,
    if m ≤ a then monomial (a - m) (AddMonoidAlgebra.coeff Q a * ((mfact a : K) / (mfact (a - m) : K))) else 0

end Formalism.IncomingBounds.Cay

namespace Formalism.IncomingBounds.Cay

open MvPolynomial Matrix Formalism.IncomingBounds

variable {K : Type} [Field K] [CharZero K]

def Mg (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (PVar n) K) :=
  Matrix.of fun i j => X (Sum.inl (i, j))

end Formalism.IncomingBounds.Cay

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.IncomingBounds.FlowDegreeBounds.Cayley =====

-- ===== clump member: Formalism.IncomingBounds.FlowDegreeBounds.LemmaF =====
-- clump-header: {"m": "Formalism.IncomingBounds.FlowDegreeBounds.LemmaF", "h": "module\n\npublic import Formalism.IncomingBounds.IncomingBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Sigma\npublic import Mathlib.Algebra.BigOperators.Ring.Finset\npublic import Mathlib.Algebra.Order.BigOperators.Group.Finset\npublic import Mathlib.Data.ZMod.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

section Helpers

variable {l d : ℕ} [NeZero d]

private theorem sum_deficit_le_Fnum_of_isDual (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D sig : ZMod d → ℝ} (hD : 0 ≤ D) (hsig : IsDual l d sig) :
    ∑ s, D s * (gam l - sig s) ≤ Fnum l d D := by
  have h := (hA l d hl hd hev D hD).2
  exact h.2 ⟨sig, hsig, rfl⟩

private theorem exists_isDual_Fnum_eq_sum_deficit (hA : LemmaFa) (hl : 3 ≤ l) (hd : 2 ≤ d) (hev : Even d)
    {D : ZMod d → ℝ} (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ Fnum l d D = ∑ s, D s * (gam l - sig s) :=
  (hA l d hl hd hev D hD).2.1

private theorem sum_add_apply_mul (D E f : ZMod d → ℝ) :
    ∑ s, (D + E) s * f s = ∑ s, D s * f s + ∑ s, E s * f s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.add_apply, add_mul]

end Helpers

theorem lemmaFc_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFc := by
  intro l d _ hl hd hev D E sig hD hE hopt
  have hDE : 0 ≤ D + E := add_nonneg hD hE
  obtain ⟨hsig, hdef⟩ := hopt
  constructor
  · have h1 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hDE hsig
    rw [sum_add_apply_mul, ← hdef] at h1
    have h2 : -(∑ s, E s * max (sig s - gam l) 0) ≤ ∑ s, E s * (gam l - sig s) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hm := le_max_left (sig s - gam l) 0
      nlinarith
    linarith
  · obtain ⟨sg, hsg, e⟩ := exists_isDual_Fnum_eq_sum_deficit hA hl hd hev hDE
    have h3 := sum_deficit_le_Fnum_of_isDual hA hl hd hev hD hsg
    have h4 : ∑ s, E s * (gam l - sg s) ≤ gam l * ∑ s, E s := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hEs : 0 ≤ E s := hE s
      have hs0 : 0 ≤ sg s := (hsg.1 s).1
      nlinarith
    rw [e, sum_add_apply_mul]
    linarith

end Formalism.IncomingBounds
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.IncomingBounds.FlowDegreeBounds.LemmaF =====

-- ===== clump member: Formalism.IncomingBounds.WeightIdentities =====
-- clump-header: {"m": "Formalism.IncomingBounds.WeightIdentities", "h": "module\n\npublic import Formalism.IncomingBounds.StatementThmP\npublic import Formalism.IncomingBounds.FlowDegreeBounds.Cayley\nimport Formalism.IncomingBounds.FlowDegreeBounds.LemmaF\nimport Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd\npublic import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.IncomingBounds

alias lemmaFa := _root_.Formalism.IncomingBounds.strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality

end Formalism.IncomingBounds
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.IncomingBounds.WeightIdentities =====
