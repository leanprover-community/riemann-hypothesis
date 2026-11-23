module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
