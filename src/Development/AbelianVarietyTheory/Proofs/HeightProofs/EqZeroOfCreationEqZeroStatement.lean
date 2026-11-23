module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → (∀ w, ∃ C : ℝ, ∀ x, ‖f (w + ι x)‖ ≤ C) → ∀ u u' : R, 0 < om u u' → hD ι π om u f - Complex.I • hD ι π om u' f = 0 → f = 0 := by
  first | exact @GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | exact GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero | (intros; apply GlobalTheory.FockCompare.eq_zero_of_creation_eq_zero <;> assumption)
