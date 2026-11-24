module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometric
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WZIsCInf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArFun_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ),
    IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (hL : ∀ i τ, (wZ (L i) t τ).IsCInf)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun (fun i => toZ (L i) t (hL i)) D Φ ↔ IsArFun L D Φ := by
  intro k _ X _ p t D hX ι _ L hL Φ
  have : Module.Finite ℤ k := hX.finite
  have H : ∀ (M : HermLB p) (τ : ℤ →+* ℂ), (wZ M t τ).IsCInf := fun M τ => _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k X p t M τ
  have hZ : IsArithVar t D := isArithVar_int k X p t D hX
  have key : ∀ (n : ι → ℤ) (a : ℝ),
      (comb (fun i => toZ (L i) t (hL i)) n).IsSelfInter a ↔ (comb L n).IsSelfInter a := by
    intro n a
    have e : (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (hL i)) n) :=
      (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb k X p t H).2 ι L n
    constructor
    · intro h₀
      obtain ⟨h, h₁, h₂⟩ := e.symm.isSelfInter hZ h₀
      exact ⟨h, (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p t D hX (comb L n) (H _) h).1 h₁, h₂⟩
    · rintro ⟨h, h₁, h₂⟩
      exact e.isSelfInter hZ ⟨h, (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p t D hX (comb L n) (H _) h).2 h₁, h₂⟩
  exact ⟨fun h => ⟨fun n => (key n _).1 (h.1 n), h.2⟩, fun h => ⟨fun n => (key n _).2 (h.1 n), h.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
