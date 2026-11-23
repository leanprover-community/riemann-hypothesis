module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

namespace UpperTheory.Gal.W2

theorem conjCharpoly_of : ConjCharpoly := by
  intro V _ _ _ d hd τ G A hτ hG
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := τ.linearEquivOfInjective hτ (by simp [hd])
  let b : Module.Basis (Fin d) ℂ V := (Pi.basisFun ℂ (Fin d)).map e.symm
  have hM : LinearMap.toMatrix b b G = A := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h1 : b j = e.symm (Pi.single j 1) := by simp [b]
    have h2 : ∀ v, b.repr v i = e v i := fun v => by simp [b, Pi.basisFun_repr]
    rw [h2, h1]
    change τ (G (e.symm (Pi.single j 1))) i = A i j
    rw [hG]
    have h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]
      exact e.apply_symm_apply _
    rw [h3, Matrix.mulVec_single_one]
    rfl
  rw [← hM, LinearMap.charpoly_toMatrix]

end UpperTheory.Gal.W2
