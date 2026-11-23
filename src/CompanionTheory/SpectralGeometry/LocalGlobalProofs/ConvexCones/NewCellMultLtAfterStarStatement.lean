module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.NewCellMultLtAfterStar
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.new_cell_mult_lt_after_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    SimpLab bar q φ lab → IsCentreSet bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
        Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
          ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar φ γ → β₀ ∈ balForms bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) < M := by
  exact @GlobalTheory.CompanionTheory.Ar.Fan.NewCellsStarMultiplicity.cellMult_lt_of_star_new
