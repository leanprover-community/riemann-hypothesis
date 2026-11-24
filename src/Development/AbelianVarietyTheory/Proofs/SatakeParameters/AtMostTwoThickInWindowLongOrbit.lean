module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.LongWindow

theorem thick_inTranslate {R : Ranks} (H : Host R) (g : R.GG) (hg : Thick H g) :
    R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv g.2) := by
  unfold Thick Host.thickPlaces at hg
  obtain ⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    simpa [Finset.mem_image] using hg
  refine ⟨s, hs, ?_⟩
  have e2 : (plc g).2 = g.2 := UpperTheory.KStar.Words.placeOf_snd g
  rw [← e2, ← e]
  rfl

theorem letter_snd {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) (k : ℕ) :
    fr.iotaInv (letter τ φ (i + k)).2 = fr.iotaInv τ.2 + (((i.val + k : ℕ) : ℤ)) • fr.iotaInv φ.2 := by
  unfold letter
  rw [UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]
  rfl

open Classical in
theorem main : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 →
    WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  intro R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩
  have hO := ((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1
    (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))
  have mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) →
      ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro k hk ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩
    rw [← letter_snd]
    exact thick_inTranslate H _ ht
  have hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆
      (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem a (by omega) ha
    · exact mem b (by omega) hb
    · exact mem c hcL hc
  have h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push_cast; omega
  have := Finset.card_le_card hsub
  omega

end GlobalTheory.HTW.LongWindow
