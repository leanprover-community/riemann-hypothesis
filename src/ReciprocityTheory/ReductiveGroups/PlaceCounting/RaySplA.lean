module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.AffineMonoid.Basic
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
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.N2

open NumberField IsDedekindDomain

theorem ncard_places_eq_finrank_iff (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E ↔
      ∀ W : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ W.asIdeal →
        W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI := Fact.mk hp
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI : Fintype (P.primesOver (𝓞 E)) := by
    rw [← IsDedekindDomain.coe_primesOverFinset hP0 (𝓞 E)]
    infer_instance
  have hsum : ∑ q : P.primesOver (𝓞 E), (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ =
      Module.finrank ℚ E := by
    rw [Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E), NumberField.RingOfIntegers.rank]
  have hiff : ∀ w : HeightOneSpectrum (𝓞 E),
      ((p : ℕ) : 𝓞 E) ∈ w.asIdeal ↔ w.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 E)) P := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simp
  let eqv := (Equiv.subtypeEquivRight hiff).trans (IsDedekindDomain.HeightOneSpectrum.equivPrimesOver (𝓞 E) hP0)
  have hS : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Fintype.card (P.primesOver (𝓞 E)) := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr eqv
  have hpos : ∀ q : P.primesOver (𝓞 E),
      1 ≤ (q : Ideal (𝓞 E)).ramificationIdx ℤ * (q : Ideal (𝓞 E)).inertiaDeg ℤ := by
    intro q
    haveI := Ideal.primesOver.isPrime P q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) _).ne' (Ideal.inertiaDeg_pos _ ℤ).ne')
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = ∑ _q : P.primesOver (𝓞 E), 1 := by simp
  have heqv : ∀ W : HeightOneSpectrum (𝓞 E), ∀ hW : ((p : ℕ) : 𝓞 E) ∈ W.asIdeal,
      ((eqv ⟨W, hW⟩ : P.primesOver (𝓞 E)) : Ideal (𝓞 E)) = W.asIdeal := by
    intro W hW
    simp [eqv, IsDedekindDomain.HeightOneSpectrum.equivPrimesOver_apply]
  rw [hS, ← hsum, hcard]
  constructor
  · intro h W hW
    have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hpos q)).1 h
    have h1 := hall (eqv ⟨W, hW⟩) (Finset.mem_univ _)
    rw [heqv W hW] at h1
    exact mul_eq_one.1 h1.symm
  · intro h
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨⟨W, hW⟩, rfl⟩ := eqv.surjective q
    rw [heqv W hW]
    obtain ⟨h1, h2⟩ := h W hW
    rw [h1, h2]

end ReciprocityTheory.ChartRestriction.N2
