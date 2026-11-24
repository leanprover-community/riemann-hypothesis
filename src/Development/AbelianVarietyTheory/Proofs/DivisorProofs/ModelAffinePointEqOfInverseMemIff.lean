module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Points

theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {z z' : X} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : ∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ z' ∈ X.basicOpen f) : z = z' := by
  have key : ∀ (x : U) (f : Γ(X, U)),
      f ∉ (hU.primeIdealOf x).asIdeal ↔ x.1 ∈ X.basicOpen f := by
    intro x f
    have e1 := hU.fromSpec_primeIdealOf x
    have e2 := hU.fromSpec_preimage_basicOpen f
    have : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x.1 ∈ X.basicOpen f := by
      rw [← e1]; rfl
    rw [← this, e2]; rfl
  have e : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩ := by
    apply PrimeSpectrum.ext
    ext f
    rw [← not_iff_not, key, key]
    exact h f
  have e1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [e] at e1
  exact e1.symm.trans e2

theorem point_eq_of_inv_mem_iff :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  intro o Ω _ _ _ M U hU z z' hz hz' h
  refine eq_of_forall_mem_basicOpen_iff hU hz hz' fun f => ?_
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have ha : valF M.pt U f ∈ M.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
  rw [← isUnit_valF_iff hz f, ← isUnit_valF_iff hz' f, isUnit_O_iff, isUnit_O_iff]
  exact and_congr_right fun h0 => h _ ha h0

end GlobalTheory.Points
