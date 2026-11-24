module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanksStatement
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

private theorem ideal_smul_map_le_of_mem {K M N : Type} [Field K]
    [AddCommGroup M] [Module K M] [Module (𝓞 K) M] [IsScalarTower (𝓞 K) K M]
    [AddCommGroup N] [Module K N] [Module (𝓞 K) N] [IsScalarTower (𝓞 K) K N]
    (ψ : M →ₗ[K] N) (L : Submodule (𝓞 K) M) (L' : Submodule (𝓞 K) N) (𝔞 : Ideal (𝓞 K))
    (h : ∀ b ∈ 𝔞, b ≠ 0 → ∀ f ∈ L, (b : K) • ψ f ∈ L') :
    𝔞 • L.map (ψ.restrictScalars (𝓞 K)) ≤ L' := by
  rw [Submodule.smul_le]
  rintro b hb _ ⟨f, hf, rfl⟩
  by_cases hb0 : b = 0
  · rw [hb0, zero_smul]
    exact L'.zero_mem
  · exact IsScalarTower.algebraMap_smul K b (ψ f) ▸ h b hb hb0 f hf

theorem degOn_add_rank_mul_degLo_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G B hU hG hB hInt hGood
  have : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  -- Reuse the canonical scalar actions without unfolding the ambient rule space during inference.
  let pts := fun S [CommRing S] [Algebra c.F S] => FrPt Xo c S
  let _ : CommRing (Rul Xo c) := rulesCommRing pts
  let _ : Module c.F (Rul Xo c) := rulesModule pts
  let _ : SMul c.F (Rul Xo c) := rulesSMul pts
  let C := cuspOn U Z G
  let C' := cuspOn U Z (G + G₀)
  let _ : AddCommGroup C := Submodule.addCommGroup C
  let _ : AddCommGroup C' := Submodule.addCommGroup C'
  let fieldModule : Module c.F C := Submodule.module C
  let fieldModule' : Module c.F C' := Submodule.module C'
  let integerModule : Module (𝓞 c.F) C := subRulesModuleInt pts C
  let integerModule' : Module (𝓞 c.F) C' := subRulesModuleInt pts C'
  let _ : SMul c.F C := fieldModule.toSMul
  let _ : SMul c.F C' := fieldModule'.toSMul
  let _ : SMul (𝓞 c.F) C := integerModule.toSMul
  let _ : SMul (𝓞 c.F) C' := integerModule'.toSMul
  have : IsScalarTower (𝓞 c.F) c.F C := subRulesTower pts C
  have : IsScalarTower (𝓞 c.F) c.F C' := subRulesTower pts C'
  obtain ⟨a, 𝔞, ha, h𝔞, hint, hsum⟩ := GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes c.F B s.lo hB s.finite_lo hInt
  obtain ⟨φ, hφ, -, hlat, -⟩ := GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral E H Dw l Xo c r U x Z G₀ s G hG
  have ⟨hGood', hrk⟩ :=
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks E H Dw l Xo c r U x D V dict Z G₀ s G hU hG hGood
  have hna : ∀ σ : c.F →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  set t : (c.F →+* ℂ) → ℝ := fun σ => ‖σ a‖ * s.cInf σ with ht
  have ht0 : ∀ σ, 0 < t σ := fun σ => mul_pos (hna σ) (s.cInf_pos σ)
  have htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ := fun σ => by
    simp only [ht, RingHom.comp_apply, Complex.norm_conj]
    rw [s.cInf_congr (CompHt.goodOf_conj σ)]
  let ψ : C ≃ₗ[c.F] C' := φ.trans (LinearEquiv.smulOfNeZero c.F C' a ha)
  have hN : ∀ σ f, normOn U x V dict Z (G + G₀) σ (ψ f) ≤ t σ * normOn U x V dict Z G σ f := by
    intro σ f
    have e : (ψ f : Rul Xo c) = a • ((f : Rul Xo c) * s.sig) :=
      congrArg (fun y : Rul Xo c => a • y) (hφ f)
    have hpet : petOn U x V dict Z (G + G₀) σ ((f : Rul Xo c) * s.sig) =
        s.cInf σ * petOn U x V dict Z G σ f :=
      GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul
        E H Dw l Xo c r U x Z G₀ s G hG f f.2.2 σ D (V (goodOf c σ)) (dict (goodOf c σ))
        (muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z)
    change petOn U x V dict Z (G + G₀) σ (ψ f) ≤
      (‖σ a‖ * s.cInf σ) * petOn U x V dict Z G σ f
    rw [e, petOn_smul, hpet, mul_assoc]
  have hL := ideal_smul_map_le_of_mem ψ.toLinearMap (latOn U Z G) (latOn U Z (G + G₀)) 𝔞
    (fun b hb hb0 f hf => by
      have hb' : (b : c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb0
      refine hlat ((b : c.F) * a) (mul_ne_zero hb' ha) (hint b hb hb0) f hf _ ?_
      exact congrArg (fun y : C' => (y : Rul Xo c))
        (@mul_smul c.F C' _ fieldModule'.toDistribMulAction.toMulAction.toSemigroupAction
          (b : c.F) a (φ f)).symm)
  have key := GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt c.F C C'
    (normOn U x V dict Z G) (normOn U x V dict Z (G + G₀)) ψ.toLinearMap t
    (latOn U Z G) (latOn U Z (G + G₀)) 𝔞 hGood.1 hGood'.1 ψ.injective ht0 htc hN
    hGood.2.1 hGood'.2.1 h𝔞 hL hrk
  have hlog : ∑ σ, Real.log (t σ) = ∑ σ : c.F →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (s.cInf σ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => Real.log_mul (hna σ).ne' (s.cInf_pos σ).ne'
  have hdeg : s.degLo - logSum B ≤ -((∑ σ, Real.log (t σ)) / (Module.finrank ℚ c.F : ℝ)) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ c.F : ℝ) := by
    rw [hlog, add_div]
    unfold TwSec.degLo lineDeg logSum
    linarith only [hsum]
  exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))) key

end GlobalTheory.FlatTw
