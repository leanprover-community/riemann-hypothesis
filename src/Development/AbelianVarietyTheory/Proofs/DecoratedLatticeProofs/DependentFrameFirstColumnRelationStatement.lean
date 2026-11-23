module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelation
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.dependent_frame_first_column_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  first | exact @GlobalTheory.DepFrame.dependent_frame_first_relation | exact GlobalTheory.DepFrame.dependent_frame_first_relation | (intros; apply GlobalTheory.DepFrame.dependent_frame_first_relation <;> assumption)
