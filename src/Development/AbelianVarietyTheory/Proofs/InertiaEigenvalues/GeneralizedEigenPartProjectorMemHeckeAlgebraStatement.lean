module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebra
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) → (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) → (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) → ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) → ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S, (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧ ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  first | exact @GlobalTheory.part_projector_mem_adjoin | exact GlobalTheory.part_projector_mem_adjoin | (intros; apply GlobalTheory.part_projector_mem_adjoin <;> assumption)
