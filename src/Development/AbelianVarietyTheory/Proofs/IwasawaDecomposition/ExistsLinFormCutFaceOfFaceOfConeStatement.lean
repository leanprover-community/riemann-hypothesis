module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfCone
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n p : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (γ' : Fin p → LinearMap.BilinForm ℤ X)
    (h₂ h₁ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    (∀ i, δ i ∈ balForms bar X) → (∀ i y, 0 ≤ δ i y y) → (∀ j, InRCone γ (γ' j)) →
    (∀ i, 0 ≤ h₂ (δ i)) → (∀ k, h₂ (γ k) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h₂ β = 0 → InRCone γ β) →
    (∀ k, 0 ≤ h₁ (γ k)) → (∀ j, h₁ (γ' j) = 0) →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h₁ β = 0 → InRCone γ' β) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (δ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → h β = 0 → InRCone γ' β := by
  first | exact @GlobalTheory.PolFan.exists_linForm_cut_face_of_face | exact GlobalTheory.PolFan.exists_linForm_cut_face_of_face | (intros; apply GlobalTheory.PolFan.exists_linForm_cut_face_of_face <;> assumption)
