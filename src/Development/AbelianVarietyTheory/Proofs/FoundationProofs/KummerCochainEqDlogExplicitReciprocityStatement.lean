module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocity
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  first | exact @GlobalTheory.RecOne.kummer_eq_dlog_one | exact GlobalTheory.RecOne.kummer_eq_dlog_one | (intros; apply GlobalTheory.RecOne.kummer_eq_dlog_one <;> assumption)
