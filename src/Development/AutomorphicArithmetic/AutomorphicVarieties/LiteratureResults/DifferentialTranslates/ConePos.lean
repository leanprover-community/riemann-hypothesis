module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ComplexOrder MatrixOrder

namespace UpperTheory.V.Lit.Dr

private theorem posDef_iff_mul_star {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.PosDef ↔ ∃ B : Matrix n n ℂ, IsUnit B ∧ M = B * star B := by
  open scoped Matrix.Norms.L2Operator in
  rw [← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]

private theorem pi_iff {n ι : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (ι → ℂ)) :
    (∃ g : GL n (ι → ℂ), g.val * 1 * star g.val = M) ↔ ∀ w, (Matrix.of fun i j => M i j w).PosDef := by
  simp only [posDef_iff_mul_star, mul_one]
  constructor
  · rintro ⟨g, rfl⟩ w
    refine ⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩
    · exact g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
    · ext i j
      simp [Matrix.mul_apply, Finset.sum_apply]
  · intro h
    choose B hB hM using h
    have hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      have := RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))
      rw [Pi.evalRingHom_apply] at this
      rw [this, ← Matrix.isUnit_iff_isUnit_det]
      exact hB w
    refine ⟨hu.unit, ?_⟩
    ext i j w
    have := congrFun (congrFun (hM w) i) j
    simp only [Matrix.of_apply] at this
    rw [this]
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem conePos : ConePos := by
  intro E _ _ a p
  refine Iff.trans ?_ (pi_iff (Matrix.of p.1))
  exact exists_congr fun g => Subtype.ext_iff

end UpperTheory.V.Lit.Dr
