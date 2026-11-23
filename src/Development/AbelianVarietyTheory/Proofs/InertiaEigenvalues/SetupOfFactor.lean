module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem setup_of_factor : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  intro D N X bkP i s hG M ι _ P d A₀ Q hA hQ A _ _ _ _ κ _ h1
  have hfin : Module.Finite (X.O0 i) A := Module.Finite.of_finite
  refine ⟨⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv B hB σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv B hB σ hσ => h1 σ fun q => ?_⟩, fun g g' hg => ?_, ?_⟩
  · by_contra hn
    have h : IsLocalRing.maximalIdeal (X.O0 i) ≤ (IsLocalRing.maximalIdeal A).comap (algebraMap (X.O0 i) A) :=
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
        Algebra.IsIntegral.isIntegral (IsLocalRing.maximalIdeal A))).ge
    exact h hn hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · rw [← map_pow]
    refine h1 _ fun q => ?_
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  · exact (hA.2.2 q).2.2.1 v hv B hB σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) B hB σ hσ
  · rw [eq_inv_iff_mul_eq_one, ← map_mul]
    refine h1 _ fun q => ?_
    rw [map_mul, (hA.2.2 q).2.1 g g' hg, inv_mul_cancel]
  · rintro z ⟨v, hv, B, hB, hz, -⟩
    exact h1 z fun q => (hA.2.2 q).2.2.2.1 v (fun hq => (hA.1 q v hq).2.2.2.1 (X.primes_subset_exceptional i hv)) B hB z hz

end GlobalTheory.NewPrime
