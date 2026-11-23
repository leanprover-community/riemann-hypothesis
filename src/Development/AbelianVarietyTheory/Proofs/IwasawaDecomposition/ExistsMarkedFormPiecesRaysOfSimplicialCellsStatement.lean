module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
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

theorem _root_.GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
  ∃ p : Fin m₀ → LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) ∧
    (∀ i, 0 < t i → p i ∈ balForms H.bar X ∧ (∀ y, 0 ≤ p i y y) ∧
      (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = p i → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (p i) = lab.evalZ (δ₀ i)) ∧
    ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ → LinearIndependent ℤ δ →
      ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
        (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
        (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_pieces_match | exact GlobalTheory.PolFan.OrbMark.exists_pieces_match | (intros; apply GlobalTheory.PolFan.OrbMark.exists_pieces_match <;> assumption)
