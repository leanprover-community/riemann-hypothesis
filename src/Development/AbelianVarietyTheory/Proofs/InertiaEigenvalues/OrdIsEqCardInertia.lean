module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.Examples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
public import GroundTheory.LocalFields.KroneckerWeber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ordIs_padic_self (l : ℕ) [Fact l.Prime] : OrdIs ℚ_[l] l 1 := by
  unfold OrdIs
  rw [IsDiscreteValuationRing.addVal_uniformizer (GroundTheory.LocalField.Padic.irreducible_natCast_integer l)]
  rfl

theorem ordIs_eq_card_inertia : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)],
    OrdIs L l (Nat.card ↥(lowerRamificationGroup ℚ_[l] L 0)) := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  have hlL : (l : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] L)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hne : ((l : 𝒪[L])) ≠ 0 := by
    intro h
    apply hlL
    have h2 : ((l : 𝒪[L]) : L) = 0 := by rw [h]; rfl
    simpa using h2
  have htop : IsDiscreteValuationRing.addVal 𝒪[L] (l : 𝒪[L]) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨E, hE⟩ := WithTop.ne_top_iff_exists.1 htop
  have hL : OrdIs L l E := by unfold OrdIs; rw [← hE]; rfl
  obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension ℚ_[l] L l E hL
  have h1 := ordIs_padic_self l
  unfold OrdIs at he h1
  have he1 : e = 1 := by
    have := he.symm.trans h1
    exact_mod_cast this
  subst he1
  rw [mul_one] at hEe
  unfold OrdIs
  rw [← hram, ← hEe, ← hE]
  rfl

end GlobalTheory.PMon.Ram
