module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegersStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem archInt_toZ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (hN : ∀ τ, (wZ N t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf) (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), ((toZ N t hN).ArchIntegrable (toZ M t hM) e hr ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → (toZ N t hN).archInt (toZ M t hM) e hr = N.archInt M e hr) := by
  intro k _ X _ p t D hX N M hN hM e r hr
  have W := fun τ : ℤ →+* ℂ => GlobalTheory.T.archIntegrable_iff_over_integers k X p t τ D hX N M (wZ N t τ) (wZ M t τ)
    (wOver_wZ N t τ) (wOver_wZ M t τ) (hN τ) e r hr
  let τ₀ : ℤ →+* ℂ := Int.castRingHom ℂ
  have hu : ∀ τ : ℤ →+* ℂ, τ = τ₀ := fun τ => Subsingleton.elim _ _
  refine ⟨⟨fun h => (W τ₀).1.1 (h τ₀), fun h τ => (W τ).1.2 h⟩, fun h => ?_⟩
  haveI : Unique (ℤ →+* ℂ) := ⟨⟨τ₀⟩, hu⟩
  unfold HermLB.archInt
  rw [finsum_unique]
  exact (W default).2 h

end GlobalTheory.CompanionTheory.Ar.BaseZ
