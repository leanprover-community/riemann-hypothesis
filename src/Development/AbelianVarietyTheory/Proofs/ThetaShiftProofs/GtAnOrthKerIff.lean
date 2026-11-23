module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpKernelIotaTorusPointsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
