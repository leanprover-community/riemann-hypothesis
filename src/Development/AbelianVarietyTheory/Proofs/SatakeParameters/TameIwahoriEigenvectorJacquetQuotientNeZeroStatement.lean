module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ), v ≠ 0 → IsIwVec θ π.π v → (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | exact GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero | (intros; apply GlobalTheory.TameIwahori.JacquetNonzero.jacquet_mk_ne_zero <;> assumption)
