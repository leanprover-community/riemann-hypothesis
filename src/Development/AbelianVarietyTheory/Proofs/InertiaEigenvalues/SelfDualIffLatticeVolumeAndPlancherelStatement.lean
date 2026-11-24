module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherel
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | exact GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | (intros; apply GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel <;> assumption)
