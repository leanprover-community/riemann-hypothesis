module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdjointSubstLogarithmsIntoParametersOfLogExponen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffsWpSubst
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffBivariateSeriesSubstPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffPadicLogSeriesUnramifiedEqZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsFrobWToC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpSNegSumBivariatePairIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusMapSubstPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstInLettersJetLogG
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstSumCMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WToCPowComm
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

theorem exists_letterCoordinates_series_onePlace : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ h5 n' _ hev B be hbe
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.TwU.exists_isFrob_wToC p
  have hb0 := GlobalTheory.BeRead.isBe0_map p σ hσ hσw be hbe
  have hb00 : MvPowerSeries.constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) = 0 := by
    by_contra h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact (hb0.axes 0 h).1 rfl
  have hD := GlobalTheory.TwU.dualOm_wToC p σ hσw n' hev B
  obtain ⟨bv, t, x, ⟨h1, h2, h3, h4⟩, hcc, hsim, ht, hx, htla, hxt⟩ :=
    Unr.exists_coords_and_series h5 hσ hb0 n' hev _ _ hD
  refine ⟨bv, h1, h2, h3, h4, fun r0 r1 U hU => ?_⟩
  obtain ⟨V, hV, hVeq⟩ := GlobalTheory.OrbitPair.expS_neg_sum_bivariate_pair_integral σ _ _ _ bv t x hb00 hcc ht hx htla hxt hsim
  obtain ⟨U2, hU2, hU2eq⟩ := GlobalTheory.OnePlacePairs.pairs_all _ bv x V hb00 hcc (fun r => (hx r).2) hV hVeq r0 r1
  obtain ⟨hξ0, hξint⟩ := GlobalTheory.OnePlace.xiE_integral (r0 := r0) (r1 := r1) x hx
  obtain ⟨hJ0, hJ⟩ := GlobalTheory.OnePlace.Letters.subst_inLetters_jetLogG (p := p) (r0 := r0) (r1 := r1) (thOne B be U)
  refine ⟨U2 * MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)), ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_mul]
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_)
    rw [norm_mul]
    exact mul_le_one₀ (hU2 _) (norm_nonneg _) (hξint _ hU _)
  · rw [hJ, GlobalTheory.OnePlaceRead.read_thOne B be hbe U _ (xiE x) hJ0 hξ0 (GlobalTheory.OnePlace.Ident.coordZ_jetZ σ hσw hev B hD t x ht (fun r => (hx r).2) htla hxt r0 r1), hU2eq]
    ring

end GlobalTheory.OnePlace

end
