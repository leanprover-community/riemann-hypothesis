module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamily
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
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.faithful_of_derivations_dualFamily : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  first | exact @GlobalTheory.faithful_of_derivations_dual_family | exact GlobalTheory.faithful_of_derivations_dual_family | (intros; apply GlobalTheory.faithful_of_derivations_dual_family <;> assumption)
