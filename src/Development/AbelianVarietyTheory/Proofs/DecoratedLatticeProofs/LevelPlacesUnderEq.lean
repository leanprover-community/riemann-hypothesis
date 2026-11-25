module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

namespace GlobalTheory.Fam.PlaceSep

variable {D : D7}

theorem natCast_mem_of_under_eq {PP PP' : Pl D.host.E}
    (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  rw [h] at h1
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP'.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (u : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem twist_prime {gp : Fin 2 → ℕ} {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces gp Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ gp i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP hP
  refine ⟨q, hq, ?_, hne⟩
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ PP.asIdeal) = q from hc] at this

theorem g_mem_of_div (P : Formalism.L2.Host.PiBar D.host) {k : Fin 2} {w : Pl D.host.E} (hw : P.Div k w) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 := P.pb_over k
  rw [← hw] at h1
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at this

end GlobalTheory.Fam.PlaceSep


open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev

  have mixed : ∀ A B : Pl D.host.E, A ∈ (pk W).Pg → QAll W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
