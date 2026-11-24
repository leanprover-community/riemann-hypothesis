module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
