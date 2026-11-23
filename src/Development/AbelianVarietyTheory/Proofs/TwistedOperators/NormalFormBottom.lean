module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RowEx.BotField

theorem field_of_gens {T Hh κ : Type} [Finite T] (v : T → Hh → κ → ℂ) (good : Set Hh)
    (hab : ∃ (H : Finset Hh) (K : Finset κ) (M₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ M₀ ∧ (∀ h ∈ H, h ∈ good) ∧
      ∀ t, ∀ h ∈ good, ∀ k, ∃ c : Hh → κ → ℂ, (∀ a b, c a b ∈ M₀) ∧ v t h k = ∑ h' ∈ H, ∑ k' ∈ K, c h' k' * v t h' k')
    (hc : ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, IsAlgebraic ℚ (v t h k / Ω)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ good, ∀ k, v t h k / Ω ∈ M := by
  obtain ⟨H, K, M₀, hM₀, hH, hv⟩ := hab
  obtain ⟨Ω, hΩ, halg⟩ := hc
  let S : Set ℂ := Set.range fun x : T × H × K => v x.1 x.2.1 x.2.2 / Ω
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  have hS : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro _ ⟨⟨t, h, k⟩, rfl⟩
    exact (halg t h (hH h h.2) k).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin hS
  refine ⟨M₀ ⊔ IntermediateField.adjoin ℚ S, inferInstance, Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨c, hc, e⟩ := hv t h hh k
  rw [e, Finset.sum_div]
  refine sum_mem fun h' hh' => ?_
  rw [Finset.sum_div]
  refine sum_mem fun k' hk' => ?_
  rw [mul_div_assoc]
  refine mul_mem ((le_sup_left : M₀ ≤ _) (hc h' k')) ((le_sup_right : IntermediateField.adjoin ℚ S ≤ _) ?_)
  exact IntermediateField.subset_adjoin ℚ S ⟨⟨t, ⟨h', hh'⟩, ⟨k', hk'⟩⟩, rfl⟩

theorem sumsIn_mono {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {A A' WW : HSp D}
    {X : Tri T A A' WW} {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SumsIn W σ X)
    (hσ : Set.range σ ⊆ Set.range σ') : SumsIn W σ' X := by
  obtain ⟨Ω, Ω', h0, h0', H⟩ := h
  exact ⟨Ω, Ω', h0, h0', fun t g hg => ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end GlobalTheory.RowEx.BotField

end
