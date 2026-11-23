module

public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RowSpan

open MvPolynomial Formalism.L2.Pj

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]


variable {σ : Type}



variable {σ : Type} (w : σ → ℕ)


theorem rowInv_map [Infinite k] {K : Type} [Field K] (φ : k →+* K) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n K (map φ P) := by
  classical
  intro σ i i' hi t
  have := GlobalTheory.RowTriangular.eval₂_shift ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) hP σ i i' hi (C t) X
    (fun ℓ => rowShift r n K σ i i' t (X ℓ)) (fun b => by simp [rowShift]) (fun ℓ hℓ => by
      rw [rowShift, aeval_X, if_neg hℓ])
  have e : ∀ Q : MvPolynomial (Letter T r n) k, rowShift r n K σ i i' t (map φ Q) =
      eval₂Hom ((C : K →+* MvPolynomial (Letter T r n) K).comp φ) (fun ℓ => rowShift r n K σ i i' t (X ℓ)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => simp [rowShift]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p s hp => simp only [map_mul, hp, map_X, eval₂Hom_X']
  rw [e, this, map_eq_eval₂Hom_C_comp]

end GlobalTheory.RowSpan
