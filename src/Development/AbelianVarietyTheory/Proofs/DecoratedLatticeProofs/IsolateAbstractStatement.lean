module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finsupp.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsolateAbstract
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eq_zero_or_exists_inverse_combination_of_separating : ∀ (X : Type) [AddCommGroup X] (Γ G : AddSubgroup X) (V : Type) [AddCommGroup V] [Module ℂ V] (T : X → V →ₗ[ℂ] V) (W : Set V) (β : X → X → ℂ) (a : X → ℂ) (χ : X → X → ℂ), Γ ≤ G → (∀ v, T 0 v = v) → (∀ x y v, T x (T y v) = β x y • T (x + y) v) → (∀ x y, β x y ≠ 0) → (∀ γ ∈ Γ, a γ ≠ 0 ∧ ∀ v ∈ W, T γ v = a γ • v) → (∀ γ ∈ Γ, ∀ x v, T γ (T x v) = χ x γ • T x (T γ v)) → (∀ x, ∀ γ ∈ Γ, ∀ γ' ∈ Γ, χ (x + γ') γ = χ x γ) → (∀ x ∈ G, ∀ y ∈ G, x - y ∉ Γ → ∃ γ ∈ Γ, χ x γ ≠ χ y γ) → ∀ (J : Finset X) (c : X → ℂ), (∀ x ∈ J, x ∈ G) → (∀ v ∈ W, ∑ x ∈ J, c x • T x v = 0) ∨ ∃ κ : X →₀ ℂ, (∀ y ∈ κ.support, y ∈ G) ∧ ∀ v ∈ W, ∑ y ∈ κ.support, κ y • T y (∑ x ∈ J, c x • T x v) = v := by
  first | exact @GlobalTheory.isolate_abstract | exact GlobalTheory.isolate_abstract | (intros; apply GlobalTheory.isolate_abstract <;> assumption)
