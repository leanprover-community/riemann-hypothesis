module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
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

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

namespace UpperTheory.V.Z.Mult

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Cp (σ : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (τ : SmIrr (GLw n w)) : Prop :=
  IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ

def At (π : CuspSub E n) (σ : Submodule ℂ (UA E n → ℂ)) : Prop :=
  ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ), Cp σ w τ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

def IsDec (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) {ι : Type}
    (σ : ι → Submodule ℂ (UA E n → ℂ)) : Prop :=
  (∀ i, IsAutRepU (σ i) ∧ (∀ v, HasWeightAt (σ i) v.embedding (lam v)) ∧ σ i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧
    iSupIndep (fun i => σ i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, σ i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K'

def CompOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU σ w) → At π σ → ∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Cp σ w τ

def Mult : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ lam : InfinitePlace E → DomWeight n,
  ∃ a : ℕ, 0 < a ∧ ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
    (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
      IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
      (∀ w ∈ S, IsSplitAt w → ∃ τ, π.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
      ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ → Nat.card {i // At π (σ i)} = a

end UpperTheory.V.Z.Mult
