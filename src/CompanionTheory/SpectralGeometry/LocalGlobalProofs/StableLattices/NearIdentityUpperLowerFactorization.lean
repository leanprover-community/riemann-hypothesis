module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis
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

@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}





theorem factor (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1

theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
