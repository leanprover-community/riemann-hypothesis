module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutGlobal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedLocalized
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
import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

open IsLocalRing

theorem LengthCutLocalizedModule.proof (hG : LengthCutGlobal.Statement.{u, max u v})
    (hL : LengthLocalizedLocalized.Statement.{u, v}) : LengthCutLocalizedModule.Statement.{u, v} := by
  intro B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf
  have hPQ : P ≤ Q₀ := hQ ▸ le_sup_left
  have hdisj : Disjoint (Q₀.primeCompl : Set B) P := Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)
  have hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime :=
    LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ
  have : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) =
      P := IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj

  have hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀)) := by
    intro h
    apply hy
    rw [← hunder]
    exact h

  have hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀) := by
    have hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ =
        Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y}) := congrArg _ hQ
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal := by
    rw [hsup]
    exact maximalIdeal.isMaximal _

  have hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp

  have hpir : IsPrincipalIdealRing
      (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI
    have : IsLocalRing (Localization.AtPrime Q₀ ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) =
        Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)} := by
      have hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) =
          maximalIdeal (Localization.AtPrime Q₀) :=
        eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup,
        Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    have hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal := ⟨⟨_, hm⟩⟩
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 1 5).mpr hprin

  have htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M,
      s • m = 0 → m = 0 := by
    intro s hs m hsm
    induction s using Localization.induction_on with
    | H x =>
    obtain ⟨a, t⟩ := x
    dsimp only at hs hsm
    have ha : a ∉ P := by
      intro ha
      apply hs
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    induction m using LocalizedModule.induction_on with
    | h m u =>
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hsm
      obtain ⟨v, hv⟩ := hsm
      simp only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv
      have hva : (v : B) * a ∉ P := fun h =>
        (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha
      rw [htf _ hva m hv, LocalizedModule.zero_mk]

  have hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M) =
      (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ :
        Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M)) := by
    rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span,
      Set.image_singleton]
  let e := (IsLocalizedModule.linearEquiv Q₀.primeCompl
    ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M))
    (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).extendScalarsOfIsLocalization
      Q₀.primeCompl (Localization.AtPrime Q₀)
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq,
    hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀)))
      (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf',
    hL B P Q₀ M hPQ]

end GroundTheory.Heights₂.Heights
