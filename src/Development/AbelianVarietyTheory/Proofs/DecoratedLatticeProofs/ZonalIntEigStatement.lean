module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalEig.zonalInt_eig | exact GlobalTheory.ZonalEig.zonalInt_eig | (intros; apply GlobalTheory.ZonalEig.zonalInt_eig <;> assumption)
