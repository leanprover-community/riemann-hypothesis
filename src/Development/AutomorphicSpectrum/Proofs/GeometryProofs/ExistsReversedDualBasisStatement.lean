module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReversedDualBasis
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.exists_reversed_dual_basis : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)),
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | exact GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis <;> assumption)
