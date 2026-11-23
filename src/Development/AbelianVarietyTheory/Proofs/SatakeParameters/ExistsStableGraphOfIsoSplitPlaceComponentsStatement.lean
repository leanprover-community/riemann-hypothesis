module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStableGraphOfIsoSplitPlaceComponents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_stable_graph_of_iso_splitPlace_components : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (s : SplitPlace L) (σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S₁ s σ₁ → IsLocS S₂ s σ₂ → Nonempty (σ₁.ρ.Equiv σ₂.ρ) → ∃ X : Submodule ℂ ((GAf L n → a.W) × (GAf L n → a.W)), X ≠ ⊥ ∧ (∀ z ∈ X, z.1 ∈ S₁ ∧ z.2 ∈ S₂) ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ z ∈ X, (NG.rt L n x z.1, NG.rt L n x z.2) ∈ X) ∧ (∀ u, ((0 : GAf L n → a.W), u) ∈ X → u = 0) ∧ (∀ u, (u, (0 : GAf L n → a.W)) ∈ X → u = 0) := by
  first | exact @GlobalTheory.LocSplitGraph.main | exact GlobalTheory.LocSplitGraph.main | (intros; apply GlobalTheory.LocSplitGraph.main <;> assumption)
