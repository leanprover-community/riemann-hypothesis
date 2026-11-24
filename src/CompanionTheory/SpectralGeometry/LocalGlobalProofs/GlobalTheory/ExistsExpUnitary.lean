module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
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

namespace GlobalTheory.CompanionTheory.UnitaryExp

open Matrix


set_option backward.isDefEq.respectTransparency false in
theorem map_exp_matrix {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (f : Matrix m m ℂ ≃ₐ[ℂ] Matrix n n ℂ) (hf : Continuous f) (S : Matrix m m ℂ) :
    f (NormedSpace.exp S) = NormedSpace.exp (f S) := by
  let _ : NormedRing (Matrix m m ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedRing (Matrix n n ℂ) := Matrix.instL2OpNormedRing
  let _ : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.instL2OpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix m m ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp f hf S

end GlobalTheory.CompanionTheory.UnitaryExp
