module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Polynomial.Vieta
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)

  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
  MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
