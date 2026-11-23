module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  first | exact @GlobalTheory.BCT.forms_decomp | exact GlobalTheory.BCT.forms_decomp | (intros; apply GlobalTheory.BCT.forms_decomp <;> assumption)
