module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquivStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeTate

theorem algebraMap_ne_zero_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (hm : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    {w : O} (hw : w ≠ 0) : algebraMap O Ω w ≠ 0 := by
  intro h0
  apply hw
  have hmem : w ∈ (mcIdeal O x).comap (C : O →+* MvPolynomial (Σ k, ι k) O) := by
    rw [Ideal.mem_comap]
    show _ = _
    have : (C w : MvPolynomial (Σ k, ι k) O) = algebraMap O _ w := rfl
    rw [this, AlgHom.commutes]
    simp [MvPolynomial.algebraMap_eq, h0]
  rw [hm.2.2.1] at hmem
  simpa using hmem

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r s n VL _ _ VO _ _ VH _ _ Lie W La om omHT T H w hw hm hLW hWL hsc
    hom hHT hex k hk1 hk2 q L Q hQ
  have hw' : algebraMap O Ω w ≠ 0 := algebraMap_ne_zero_of_model hm hw
  have hscale : ∀ s, mseg x s ≠ 0 → ∀ v ∈ La.lat s, algebraMap O Ω w • v ∈ Lie.lat s :=
    fun s hs v hv => (hsc s hs _).2 ⟨v, hv, rfl⟩
  have sWLa : SameGeneric O x W La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hWL s hs hv⟩,
      fun v hv => ⟨w, hw, hLW s hs (hscale s hs v hv)⟩⟩
  have sLaW : SameGeneric O x La W := fun s hs => ⟨(sWLa s hs).2, (sWLa s hs).1⟩
  have sLieW : SameGeneric O x Lie W := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hLW s hs hv⟩,
      fun v hv => ⟨w, hw, hscale s hs v (hWL s hs hv)⟩⟩
  have sWLie : SameGeneric O x W Lie := fun s hs => ⟨(sLieW s hs).2, (sLieW s hs).1⟩
  have sLaLa : SameGeneric O x La La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have h1 := GlobalTheory.T.chart_bundle_extension_intersection O Ω K ι x d r n s VL VH VO La W H T om omHT hm sLaW hHT hom hex k hk1 hk2
    q L Q hQ
  have h2 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL La W Lie hm sLaW sWLie k hk1 hk2 q L Q hQ).1
  have h3 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL Lie W Lie hm sLieW sWLie k hk1 hk2 q L Q hQ).2
  have h4 := (GlobalTheory.T.dvr_bundle_statement_d O Ω K ι x d r VL La Lie w hw hm hsc k hk1 hk2 q L Q hQ).1
  have hcarry : ∀ s, mseg x s ≠ 0 → ∀ v,
      ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) ∧
        ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) := by
    intro s hs v
    have : (LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s := by
      rw [LinearEquiv.smulOfNeZero_apply, hsc s hs]
      constructor
      · rintro ⟨e, he, hve⟩
        rwa [smul_right_injective VL hw' hve]
      · exact fun hv => ⟨v, hv, rfl⟩
    exact ⟨this, this⟩
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have h5 := (GlobalTheory.T.same_generic_linear_equiv O Ω K ι x d hm r VL VL (LinearEquiv.smulOfNeZero Ω VL _ hw') La La Lie Lie
    sLaLa hcarry).2 (k - 1) (psum (Fin r) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum r (k - 1)) (by omega) q L Q hQ' w hw
  rw [h5]
  linarith

end GlobalTheory.CompanionTheory.Ar.Num.HodgeTate
