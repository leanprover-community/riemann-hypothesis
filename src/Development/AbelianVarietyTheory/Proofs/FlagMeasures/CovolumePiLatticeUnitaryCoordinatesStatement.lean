module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinates
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
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.covolume_pi_lattice_unitary_coordinates : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  first | exact @GlobalTheory.CovPi.covolume_pi_unitary | exact GlobalTheory.CovPi.covolume_pi_unitary | (intros; apply GlobalTheory.CovPi.covolume_pi_unitary <;> assumption)
