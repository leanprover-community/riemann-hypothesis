module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationAppr
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), (∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → SpLink A e χ (fun r s x => Y r s x 1) y := by
  exact @GlobalTheory.KZ.spLink_of_spec_approx
