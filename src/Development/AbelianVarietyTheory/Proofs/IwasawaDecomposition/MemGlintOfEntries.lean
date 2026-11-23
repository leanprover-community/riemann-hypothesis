module

public import Formalism.SatakeDualWeyl.Statement
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

namespace GlobalTheory.MemGlintOfEntries

theorem mem_glint_of_entries {K : Type} [inst : Field K] {n : ℕ} (O : Subring K)
    (g : GL (Fin n) K)
    (h : ∀ (i j : Fin n), (↑g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h' : ∀ (i j : Fin n), (↑g⁻¹ : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  let B : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h' i j⟩
  have hA : O.subtype.mapMatrix A = (↑g : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hB : O.subtype.mapMatrix B = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hinj : Function.Injective
      (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) K) := by
    intro X Y hXY
    ext i j
    exact congrFun (congrFun hXY i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul g
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.MemGlintOfEntries
