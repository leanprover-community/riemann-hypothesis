module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [if_pos h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [if_pos (hdiv.mpr hd), if_pos ⟨h0, hd⟩]
    · rw [if_neg (fun h => hd (hdiv.mp h)), if_neg (fun h => hd h.2)]
  · rw [if_neg h0, map_zero, if_neg (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

end GroundTheory.Heights₂.Heights.RestTerms
