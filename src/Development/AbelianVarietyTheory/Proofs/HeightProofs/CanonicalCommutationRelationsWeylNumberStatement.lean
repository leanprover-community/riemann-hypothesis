module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumber
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.canonicalCommutationRelations_weylNumber : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  first | exact @GlobalTheory.WeylNumber.weyl_number | exact GlobalTheory.WeylNumber.weyl_number | (intros; apply GlobalTheory.WeylNumber.weyl_number <;> assumption)
