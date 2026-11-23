module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLatticeVacuumEigen
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.schroedingerOperator_heisenbergLatticeVacuum_eigen : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1) →
    ∀ w ∈ Λ, GlobalTheory.WeilM.schr ψ₀ w (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) = χ w • GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ := by
  first | exact @GlobalTheory.HeisLatVac.schr_vacFn | exact GlobalTheory.HeisLatVac.schr_vacFn | (intros; apply GlobalTheory.HeisLatVac.schr_vacFn <;> assumption)
