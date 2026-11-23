module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

theorem standardHermitian_gram_posDef (σ : K →+* ℂ) {m n : ℕ} (v : Fin n → Fin m → K)
    (hv : LinearIndependent K v) :
    (Matrix.of fun i j => ∑ k, starRingEnd ℂ (σ (v i k)) * σ (v j k)).PosDef := by
  classical

  let Vt : Matrix (Fin m) (Fin n) K := Matrix.of fun k j => v j k
  let B : Matrix (Fin m) (Fin n) ℂ := Vt.map σ
  have hker : LinearMap.ker (Matrix.toLin' Vt) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ j, g j • v j = 0 := by
      ext k
      have := congrFun hg k
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Vt, Matrix.of_apply,
        Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j
    exact Fintype.linearIndependent_iff.1 hv g h0 j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hW : LinearMap.toMatrix' g * Vt = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Vt, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hB : (LinearMap.toMatrix' g).map σ * B = 1 := by
    simp only [B]
    rw [← Matrix.map_mul, hW, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
    simp only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] at this
    exact this
  convert Matrix.PosDef.conjTranspose_mul_self B hinj using 1
  ext i j
  simp [Matrix.mul_apply, B, Vt]

def stdLat (m : ℕ) : Submodule (𝓞 K) (Fin m → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin m => (Pi.single i 1 : Fin m → K))

end ReciprocityTheory.GeometryOfNumbersTheory
