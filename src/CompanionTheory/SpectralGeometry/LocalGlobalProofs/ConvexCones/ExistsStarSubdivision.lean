module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsStarOfClausesStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthTwistedGaloisStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCellStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarIntegralValuesPolyhedralStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StrictStarFunctionBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFanStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision

theorem isTwG_starFun {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O} {ψ w : InvFun O}
    (hψ : IsTwG w0 ψ) (hd : IsTwG w0 (starDepth bar ψ w)) (K D : ℕ) :
    IsTwG w0 (starFun bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

theorem exists_starSubdivision : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 w → IsCentreSet bar q ψ w → ∃ ψ' : InvFun O, IsPolyFan bar q ψ' ∧ IsTwG w0 ψ' ∧ Subordinate bar q ψ' ψ ∧ IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar w0 hb q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := GlobalTheory.T.strict_star_function_bounds O bar hb q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.star_function_linear_on_cell O bar hb q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell bar (starFun bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell bar (starFun bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf bar q ψ w (starFun bar ψ w K D) := GlobalTheory.T.is_star_of_clauses O bar hb q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun bar ψ w K D, GlobalTheory.T.star_integral_values_polyhedral O bar hb q ψ w _ hψ hW hstar hint hpos,
    isTwG_starFun htψ (GlobalTheory.T.star_depth_twisted_galois O bar w0 hb ψ w htψ htw) K D, GlobalTheory.T.starSubdivision_subordinate_to_fan _ bar q ψ w _ hstar, hstar⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision
