module

public import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Statement
import GroundTheory.ProfiniteCohomology.ProcyclicDefs
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.LocalUnram


open GroundTheory.LocalField.Abstract in
theorem continuous_of_additive_of_frobenius_eq_one :
    ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (χ : Gal(Ω/K) → ZMod n),
      (∀ g h, χ (g * h) = χ g + χ h) →
      (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → Continuous χ := by
  intro K Ω _ _ _ _ _ _ _ n _ χ hadd h1
  obtain ⟨hcont, hsurj, -⟩ := unramifiedDegree_spec (K := K) (Ω := Ω)
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, NeZero.pos n⟩, rfl⟩
  have hone : χ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ g, χ g⁻¹ = -χ g := fun g => by
    have h := hadd g⁻¹ g
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hpow : ∀ (g : Gal(Ω/K)) (k : ℕ), χ (g ^ k) = k • χ g := fun g k => by
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]
  obtain ⟨f, hf⟩ := hsurj (Multiplicative.ofAdd 1)
  have hχf : χ f = 1 := h1 f hf
  have hker : ∀ g, unramifiedDegree K Ω g = 1 → χ g = 0 := fun g hg => by
    have h := h1 (g * f) (by rw [map_mul, hg, one_mul, hf])
    rw [hadd, hχf] at h
    exact add_eq_right.mp h
  have key : ∀ g, χ g = ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) := by
    intro g
    set x := Multiplicative.toAdd (unramifiedDegree K Ω g) with hx
    set k : ℕ := (ProfiniteInteger.proj N x).val with hk
    have hkc : ((k : ℕ) : ZMod (N : ℕ)) = ProfiniteInteger.proj N x := ZMod.natCast_zmod_val _
    have hz : ProfiniteInteger.proj N (x - (k : ProfiniteInteger)) = 0 := by
      rw [map_sub, map_natCast, hkc, sub_self]
    obtain ⟨w, hw⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero hz
    obtain ⟨t, ht⟩ := hsurj (Multiplicative.ofAdd w)
    have hdeg : unramifiedDegree K Ω (g * (f ^ k)⁻¹ * (t ^ (N : ℕ))⁻¹) = 1 := by
      simp only [_root_.map_mul, _root_.map_inv, _root_.map_pow, hf, ht]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_pow, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd,
        toAdd_one, ← hx, ← hw, nsmul_eq_mul, mul_one]
      ring
    have h0 := hker _ hdeg
    rw [hadd, hadd, hinv, hinv, hpow, hpow, hχf] at h0
    have hN : (N : ℕ) • χ t = 0 := by simp
    rw [hN, neg_zero, add_zero, nsmul_eq_mul, mul_one, hkc] at h0
    exact add_neg_eq_zero.mp h0
  have hχ : χ = fun g => ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω g)) :=
    funext key
  rw [hχ]
  exact (ProfiniteInteger.continuous_proj N).comp (continuous_toAdd.comp hcont)

end GlobalTheory.CompanionTheory.LocalUnram
