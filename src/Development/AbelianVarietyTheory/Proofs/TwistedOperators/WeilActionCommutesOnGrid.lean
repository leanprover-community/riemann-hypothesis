module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem natCast_not_mem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hn) (w.asIdeal.mul_mem_left _ hp)

theorem natCast_mem_w {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) {n : ℕ} (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
  rw [← P.under_w hv] at hn
  have h : (n : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (P.w v).asIdeal := hn
  rwa [Ideal.mem_comap, map_natCast] at h

end GlobalTheory.SquareComm

namespace GlobalTheory.SquareComm

open GlobalTheory.RowClaim

theorem squareStanding_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {large₂ : SizeData₂ D}
    {R : RealDat D A Ks} {F : Face D A} (s : HidaSetting large₂ R F) (h11 : 11 ≤ D.host.splitBound) {sc : Consts}
    (G : GridData R.toLevCh sc) (t : T) : SquareStanding G t := by
  classical
  refine ⟨h11, fun w hw => ?_⟩
  obtain ⟨⟨Pm, -, -⟩, -⟩ := s.size
  have hq := D.host.hyp.1
  have hd := D.host.hyp.2.1
  have cop : ∀ p ∈ D.host.levelPrimes, p.Prime →
      Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) p := by
    intro p hpl hp
    exact Nat.Coprime.mul_left (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (Pm.level_split p hpl)).symm
      (D.host.ccK_coprime p (by simp [hpl]))
  have cop0 : Nat.Coprime (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) (q0 D) := by
    obtain ⟨hp0, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
    have c1 : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
      rw [Nat.Coprime, Nat.gcd_rec, hm]
      simp
    refine Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left ⟨Formalism.MainNotions.rPrAv D, by unfold LevelStarExponents.condE; ring⟩ c1) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hp0).2 hn).symm
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
    · exact natCast_not_mem_of_coprime _ cop0 (natCast_mem_w G.pl hv G.pl.basePlace_over_qZero)
    · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 0) (D.host.g_prime 0)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ (D.host.g_level 1) (D.host.g_prime 1)) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.1 D.host.pde_prime) (natCast_mem_w G.pl hv h)
      · exact natCast_not_mem_of_coprime _ (cop _ D.host.pde_level.2 D.host.pde'_prime) (natCast_mem_w G.pl hv h)
  · have h1 := (s.core.lev.Q_off t w hw).1
    have h2 := s.guard.2 t w hw
    simp only [Nat.cast_mul, w.isPrime.mul_mem_iff_mem_or_mem, not_or] at h1 h2 ⊢
    tauto

end GlobalTheory.SquareComm
