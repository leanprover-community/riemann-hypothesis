module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfIntertwinesUpToScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.ConjNormPow

theorem absNorm_comap_equiv {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem absNorm_maxPowDividing_conjPl : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (N : ℕ), Ideal.absNorm ((Formalism.L2.DIV.conjPl P).maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) := by
  intro D P N
  classical
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingEquiv.ofRingHom Formalism.L2.DIV.starOHom Formalism.L2.DIV.starOHom
    (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a) (RingHom.ext fun a => Formalism.L2.DIV.starO_starO a)
  have hc : (Formalism.L2.DIV.conjPl P).asIdeal = P.asIdeal.comap σ := rfl
  set J : Ideal (𝓞 D.host.E) := Ideal.span {((N : ℕ) : 𝓞 D.host.E)} with hJdef
  have hJ : J.comap σ = J := by
    rw [← Ideal.map_symm, hJdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hpow : ∀ k : ℕ, (P.asIdeal.comap σ) ^ k = (P.asIdeal ^ k).comap σ := by
    intro k
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  have hiff : ∀ k : ℕ, J ≤ (P.asIdeal.comap σ) ^ k ↔ J ≤ P.asIdeal ^ k := by
    intro k
    rw [hpow, ← hJ, Ideal.comap_le_comap_iff_of_surjective _ σ.surjective, hJ]
  have hcount : (Associates.mk (Formalism.L2.DIV.conjPl P).asIdeal).count (Associates.mk J).factors =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
    by_cases hJ0 : J = ⊥
    · rw [hJ0, ← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
      simp only [Associates.count]
      split_ifs <;> rfl
    have hm : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ0
    have key : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ),
        k ≤ (Associates.mk Q.asIdeal).count (Associates.mk J).factors ↔ J ≤ Q.asIdeal ^ k := by
      intro Q k
      rw [← Associates.prime_pow_dvd_iff_le hm (Associates.irreducible_mk.mpr Q.irreducible),
        ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
    apply le_antisymm
    · rw [key P, ← hiff, ← hc, ← key]
    · rw [key (Formalism.L2.DIV.conjPl P), hc, hiff, ← key]
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  rw [hcount, hc, hpow, absNorm_comap_equiv]

end GlobalTheory.ConjNormPow
