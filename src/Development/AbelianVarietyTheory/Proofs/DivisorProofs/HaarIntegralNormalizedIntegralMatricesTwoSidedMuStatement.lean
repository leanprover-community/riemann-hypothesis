module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w (n := a) → B ∈ GlobalTheory.LFun.KGL w (n := b) →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  first | exact @GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | exact GlobalTheory.BCT.HintInv.hint_intMat_mul_mul | (intros; apply GlobalTheory.BCT.HintInv.hint_intMat_mul_mul <;> assumption)
