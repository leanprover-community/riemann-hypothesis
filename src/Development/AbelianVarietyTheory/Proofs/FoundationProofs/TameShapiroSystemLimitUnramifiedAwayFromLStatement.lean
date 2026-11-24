module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromL
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

theorem _root_.GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (n e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (Yt : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (q : Pl) (B : ValuationSubring Ω),
  ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → IsPlaceOver B q → (∀ s ∈ Ine (F := ℚ) B, ψ s = 1 ∧ θ s = 1) →
  Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) →
  (∀ r x, χ r x ∈ c.O) →
  (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) →
  (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) →
  (∀ r s a i, ‖Yt s a i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  ∃ v : Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, ∀ a, Yt s a = mat W s *ᵥ v a - v a := by
  first | exact @GlobalTheory.KA.TameUnr.tame_limit_unram | exact GlobalTheory.KA.TameUnr.tame_limit_unram | (intros; apply GlobalTheory.KA.TameUnr.tame_limit_unram <;> assumption)
