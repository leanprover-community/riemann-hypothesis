module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGenerator
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

theorem _root_.GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  first | exact @GlobalTheory.CocWildTame.eq_zero_on_Ine | exact GlobalTheory.CocWildTame.eq_zero_on_Ine | (intros; apply GlobalTheory.CocWildTame.eq_zero_on_Ine <;> assumption)
