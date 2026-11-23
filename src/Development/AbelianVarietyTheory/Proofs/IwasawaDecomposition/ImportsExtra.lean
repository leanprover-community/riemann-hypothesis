module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace GlobalTheory.IsolatedTheoremFive

theorem main {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (h : Function.Injective (Matrix.mulVec E)) :
    Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  have hl : LinearMap.ker (Matrix.mulVecLin E) = ⊥ := LinearMap.ker_eq_bot.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin E) hl
  have hB : LinearMap.toMatrix' g * E = 1 := by
    have e : Matrix.mulVecLin E = Matrix.toLin' E := rfl
    have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin E) = LinearMap.toMatrix' g * E := by
      rw [LinearMap.toMatrix'_comp, e, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hB' : (LinearMap.toMatrix' g).map φ * E.map φ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero φ) (map_one φ)]
  intro x y hxy
  have := congrArg (Matrix.mulVec ((LinearMap.toMatrix' g).map φ)) hxy
  simpa [Matrix.mulVec_mulVec, hB'] using this

theorem target : ∀ {K K' : Type} [inst : Field K] [inst_1 : Field K'] (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K), Function.Injective (Matrix.mulVec E) → Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  intro K K' _ _ φ n d E h
  exact main φ E h

end GlobalTheory.IsolatedTheoremFive
