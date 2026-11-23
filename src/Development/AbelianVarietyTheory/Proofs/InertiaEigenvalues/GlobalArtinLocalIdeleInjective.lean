module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfApproxByCongruentGlobalUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalApproxOfArtinTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEqOneOfCongruentGlobalApproxStatement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinLocalInj

theorem artin_localIdele_injective : ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ w : HeightOneSpectrum (𝓞 E), Function.Injective fun x : (w.adicCompletion E)ˣ => art (Neutral.B1.localIdele E w x) := by
  intro hC E Ω _ _ _ _ _ art ha w
  have hker : ∀ x : (w.adicCompletion E)ˣ, art (Neutral.B1.localIdele E w x) = 1 → x = 1 := by
    intro x hx
    have hx' : art (Neutral.B1.localIdele E w x⁻¹) = 1 := by rw [map_inv, map_inv, hx, inv_one]
    have hv : Valued.v (x : w.adicCompletion E) = 1 := by
      rcases le_total (Valued.v (x : w.adicCompletion E)) 1 with h | h
      · exact GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w x x.ne_zero h (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx)
      · have h2 : Valued.v ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀]
          exact inv_le_one_of_one_le₀ h
        have h3 := GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w _ (x⁻¹).ne_zero h2 (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x⁻¹ hx')
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at h3
        exact h3
    exact Units.ext (GlobalTheory.T.eq_one_of_approx_by_congruent_global_units hC E w x hv (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx))
  intro x y hxy
  have : art (Neutral.B1.localIdele E w (x * y⁻¹)) = 1 := by
    simp only at hxy
    rw [map_mul, map_mul, map_inv, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ this)

end GlobalTheory.ArtinLocalInj
