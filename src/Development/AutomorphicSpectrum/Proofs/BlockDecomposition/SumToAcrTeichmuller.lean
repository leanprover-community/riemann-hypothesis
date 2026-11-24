module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.MapUgCToUg
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LcNatProof

theorem natCast_val_castHom {R : Type} [CommRing R] (l n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ (n + 1))]
    (h : (l : R) ^ n = 0) (a : ZMod (l ^ (n + 1))) :
    (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : R) = (a.val : R) := by
  have key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) =
      (a.val : ZMod (l ^ n)) := by
    rw [ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))),
      ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)
  have e := congrArg (Int.cast : ℤ → R) hc
  push_cast at e
  rw [h, zero_mul, sub_eq_zero] at e
  exact e.symm

variable {l : ℕ} [Fact l.Prime]

theorem sum_toAcr_teichmuller (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) (n : ℕ) :
    ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
  have hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W)) :=
    { idem := fun a => by
        change WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)
        rw [← map_mul, (he.idem a).eq]
      ortho := fun i j hij => by
        change WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W)) := hO.isIdempotentElem_sum
  have hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) := hE.one_sub
  have hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0 := by

    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)
  have ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))) := hu.map (A.toAcr n)
  have h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0 := by
    rw [← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n,
      zero_mul, mul_zero]

  rw [map_sub, map_one, map_sum, sub_eq_zero] at h0
  exact h0.symm

theorem lcNat : LcIdem → LcSpec → LcNat := by
  intro hId hSp l _ H A hA n
  refine ⟨?_, ?_⟩
  · intro B hB φ h g hg f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ n)) f
    have h1 := (hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)
    have hφ : CompleteOrthogonalIdempotents (φ ∘ e) := he.map φ
    have h2 := (hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by
      refine (hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_
      have := hg (e a) (he.idem a)
      change algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal
      rw [← this]
      exact hm)

    rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]
    rfl
  · intro f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ (n + 1))) f
    have h1 := (hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)
    set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef
    have hL := (hSp l H A hA n).1 (f.map c)
    have hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) =
        A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n) := fun a => by
      rw [hL (e a) (c a) (he.idem a) (fun p hp => by
        change c (f p) = c a
        rw [(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]

    rw [h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT a, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.LcNatProof
