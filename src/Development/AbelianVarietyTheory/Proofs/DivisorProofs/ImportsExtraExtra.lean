module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
