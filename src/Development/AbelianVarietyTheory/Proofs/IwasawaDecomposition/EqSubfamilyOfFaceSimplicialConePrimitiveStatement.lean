module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  first | exact @GlobalTheory.PolFan.eq_subfamily_of_face | exact GlobalTheory.PolFan.eq_subfamily_of_face | (intros; apply GlobalTheory.PolFan.eq_subfamily_of_face <;> assumption)
