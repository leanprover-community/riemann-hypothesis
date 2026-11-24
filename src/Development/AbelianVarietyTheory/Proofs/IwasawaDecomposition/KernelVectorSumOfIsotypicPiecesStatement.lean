module

public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelVectorSumOfIsotypicPieces
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


theorem _root_.GlobalTheory.T.kernel_vector_sum_of_isotypic_pieces : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  first | exact @GlobalTheory.decomp_kernels_isotIn | exact GlobalTheory.decomp_kernels_isotIn | (intros; apply GlobalTheory.decomp_kernels_isotIn <;> assumption)
