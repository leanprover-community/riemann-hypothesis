module

public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.smooth_admissible_unitary_mem_sup_isotypic_parts : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x})) → (∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x) → ∀ x ∈ C, x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π := by
  first | exact @GlobalTheory.SpanIsot.span_isotIn | exact GlobalTheory.SpanIsot.span_isotIn | (intros; apply GlobalTheory.SpanIsot.span_isotIn <;> assumption)
