module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EqOfOrbitMarkInCellCone
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.eq_of_orbit_mark_in_cell_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), IsTwG w0 φ → IsTwG w0 lab →
  SimpLab bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun O w0 v).evalZ β = 1 → (OrbMark.orbFun O w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkUniqueInCell.eq_of_orbMark_of_inRCone_cell <;> assumption)
