module

public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.WeightCongruences.RootOfUnityGaloisActionCMDatum
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions

private theorem prod_pair {G : Type*} [Group G] [Fintype G] {M : Type*} [CommMonoid M]
    (s : G) (hs1 : s ≠ 1) (hs2 : s * s = 1) (f : G → M) (hf : ∀ g, f g * f (g * s) = 1) :
    ∏ g, f g = 1 := by
  refine Finset.prod_involution (fun g _ => g * s) (fun g _ => hf g) ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro g _ _ h
    apply hs1
    simpa using h
  · intro g _
    rw [mul_assoc, hs2, mul_one]

private theorem phase_pair (w : ℂ) (m : ℕ) (hm : 0 < m) (hw : w ^ m = 1) (hz : 1 + w ≠ 0) :
    (1 + w) / ((‖1 + w‖ : ℝ) : ℂ) * ((1 + w⁻¹) / ((‖1 + w⁻¹‖ : ℝ) : ℂ)) = 1 := by
  have hn : ‖w‖ = 1 := by
    have h := congrArg (‖·‖) hw
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hm.ne').1 h
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    have : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn, one_pow]
    rw [Complex.inv_def, this, inv_one, Complex.ofReal_one, mul_one]
  have hconj : 1 + w⁻¹ = (starRingEnd ℂ) (1 + w) := by
    rw [hinv, map_add (f := _), map_one]
  rw [hconj, Complex.norm_conj]
  set a := 1 + w with ha
  have hna : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem UpperTheory.prod_cmType_phase_one_add_rootOfUnity :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → z ≠ -1 →
      ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (1 + z) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (1 + z)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz hzne
  letI : Fintype R.Psi := Fintype.ofEquiv ι eT
  set F : R.Psi → ℂ := fun p =>
    H.emb (p : R.GG) (1 + z) / ((‖H.emb (p : R.GG) (1 + z)‖ : ℝ) : ℂ) with hF
  change ∏ τ, F (eT τ) = 1
  rw [Equiv.prod_comp eT F]
  obtain ⟨m, hm, hzm⟩ := hz
  have hsg := (UpperTheory.rootOfUnity_galois_action_CMDatum R.toFrame H.toHostAx z ⟨m, hm, hzm⟩).2.2
  refine prod_pair ⟨R.sg, R.sg_mem_Psi⟩ ?_ ?_ F ?_
  · intro h
    exact R.sg_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext R.sg_mul_sg
  · intro g
    have hz1 : 1 + z ≠ 0 := by
      intro h
      apply hzne
      linear_combination h
    have key : H.emb ((g * ⟨R.sg, R.sg_mem_Psi⟩ : R.Psi) : R.GG) (1 + z)
        = 1 + (H.emb (g : R.GG) z)⁻¹ := by
      simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, Subgroup.coe_mul, map_mul,
        RingHom.comp_apply]
      change H.φ₀ ((H.gal.symm (g : R.GG) * H.gal.symm R.sg) (1 + z))
        = 1 + (H.φ₀ ((H.gal.symm (g : R.GG)) z))⁻¹
      rw [AlgEquiv.mul_apply, map_add (f := _), map_one, hsg, map_add (f := _), map_one, map_inv₀, map_add (f := _),
        map_one, map_inv₀]
    have hne : 1 + H.emb (g : R.GG) z ≠ 0 := by
      have : H.emb (g : R.GG) (1 + z) ≠ 0 := (map_ne_zero _).2 hz1
      simpa using this
    simp only [hF, key]
    have e1 : H.emb (g : R.GG) (1 + z) = 1 + H.emb (g : R.GG) z := by simp
    rw [e1]
    exact phase_pair _ m hm (by rw [← map_pow, hzm, map_one]) hne
