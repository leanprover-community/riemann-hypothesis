module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthLeDividedPowerContentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem natCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    refine le_trans (le_min ih (by simp)) (v.map_add _ _)

theorem intCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  cases n with
  | ofNat k => simpa using natCast_isInt v k
  | negSucc k =>
    rw [Int.cast_negSucc, v.map_neg]
    exact_mod_cast natCast_isInt v (k + 1)

theorem detDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C),
    IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧
    detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  intro C _ _ v p hp hv i d c G u hu
  obtain ⟨hhom, hint, -, -⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have h0 : 0 ≤ detDepth G u c := by
    unfold detDepth
    exact GlobalTheory.T.depth_nonneg_integral_operator_integral_vectors C v (Fin i) (fun _ => d) (fun _ => G) (fun _ => Fin i) (fun _ => u)
      (detPow C i c) (fun _ a e => hu.1 a e)
      (fun α => by obtain ⟨n, hn⟩ := hint α; rw [hn]; exact intCast_isInt v n)
  have h1 : detDepth G u c ≤ content v (detPow C i c) := by
    unfold detDepth
    exact GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent C v (Fin i) (fun _ => d) (fun _ => i) (fun _ => G) (fun _ => u)
      (detPow C i c) (i * c) hhom (fun _ => hu)
  exact ⟨h0, h1, h1.trans (GlobalTheory.T.dividedPowerContentValuation_detPow_bounds C v p hp hv i c).1⟩

end GlobalTheory.FGDepth
