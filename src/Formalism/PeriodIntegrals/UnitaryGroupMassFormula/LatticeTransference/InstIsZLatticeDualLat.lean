module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Formalism.LatticeTheta.ThetaShiftInversion
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module

noncomputable section

namespace PI.Tr

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dualLat_eq (Λ : Submodule ℤ E) :
    dualLat Λ = LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  show (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) ↔ _
  refine forall₂_congr fun x _ => ?_
  rw [innerₗ_apply_apply, real_inner_comm, Submodule.mem_one]
  simp only [algebraMap_int_eq, eq_intCast]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

section lattice

variable [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

instance instDiscreteDualLat : DiscreteTopology (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [dualLat_eq]
  exact (Formalism.H.dualIsLattice E Λ).1

end lattice

end PI.Tr
