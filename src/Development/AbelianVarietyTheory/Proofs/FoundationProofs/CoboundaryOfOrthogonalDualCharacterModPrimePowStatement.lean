module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfOrthogonalDualCharacterModPrimePow
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  first | exact @GlobalTheory.Ord2.LocCharPerfect.perfect | exact GlobalTheory.Ord2.LocCharPerfect.perfect | (intros; apply GlobalTheory.Ord2.LocCharPerfect.perfect <;> assumption)
