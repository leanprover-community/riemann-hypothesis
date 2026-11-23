module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

@[expose] public section

namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
