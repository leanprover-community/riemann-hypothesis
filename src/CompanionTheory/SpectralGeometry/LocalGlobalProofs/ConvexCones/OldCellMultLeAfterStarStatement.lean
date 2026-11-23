module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.OldCellMultLeAfterStar
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.old_cell_mult_le_after_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → SimpLab bar q φ lab → ∀ M : ℕ, maxMult bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim bar (⟨γ' i, hγ'.mem i⟩ : balForms bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → IsCell bar ψ' γ →
          (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell bar φ γ', cellMult bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms bar X)) ≤ M ∧
            ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le | exact GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.OldCellsStarMultiplicity.starOld_cell_mult_le <;> assumption)
