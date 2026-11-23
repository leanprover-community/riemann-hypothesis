module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairingLocallyConstant
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cocycle_pairing_locally_constant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → (toGS Ω (S : Set Pl)).ker ≤ N0g W ⊓ ψ.ker → IsLocallyConstant ψ → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, y a = 0 ∧ z a = 0 ∧ Cv n (d a) 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Coc2 c n S (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) := by
  first | exact @GlobalTheory.Ord2.cup_product_two_cocycle | exact GlobalTheory.Ord2.cup_product_two_cocycle | (intros; apply GlobalTheory.Ord2.cup_product_two_cocycle <;> assumption)
