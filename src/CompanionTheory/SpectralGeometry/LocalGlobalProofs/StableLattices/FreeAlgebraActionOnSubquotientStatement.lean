module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
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
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.free_algebra_action_on_subquotient : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C), (∀ k, ∀ z ∈ Z, l k z ∈ Z) → (∀ k, ∀ z ∈ B, l k z ∈ B) →
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | exact GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.QuotAction.descends <;> assumption)
