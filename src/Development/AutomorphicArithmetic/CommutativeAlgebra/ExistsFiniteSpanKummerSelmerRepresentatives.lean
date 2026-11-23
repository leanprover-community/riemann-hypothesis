module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import GroundTheory.FunctionField.DivisorDegree
public import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.FunctionField.Divisor

@[expose] public section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : divisor (x ^ n) = n • (divisor x : Divisor k K) := by
  induction n with
  | zero => simp [divisor_one]
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

theorem UpperTheory.exists_finite_span_kummerSelmer_representatives :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], ∃ (n : ℕ) (v : Fin n → K), ∀ f ∈ SelAll k K q, ∃ g ∈ SelAll k K q, (∃ c : Fin n → k, (g : K) = ∑ i, c i • v i) ∧ ∃ u : Kˣ, f = g * u ^ q := by
  intro k K _ _ _ _ _ q _
  obtain ⟨x, hxt, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hd : 0 < Module.finrank (IntermediateField.adjoin k ({x} : Set K)) K := Module.finrank_pos
  obtain ⟨γ, hγ⟩ := Divisor.exists_bound_deg_sub_finrank_L (k := k) (K := K)
  set n := γ.toNat + 1
  set E : Divisor k K := n • poleDivisor x with hE
  have hdegE : (n : ℤ) ≤ Divisor.deg E := by
    rw [hE, map_nsmul, Divisor.deg_poleDivisor hxt, nsmul_eq_mul]
    nlinarith
  set V := (q • E).L with hV
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun i => (b i : K), ?_⟩
  intro f hf
  have hf' : ∀ w : Place k K, (q : ℤ) ∣ w.ord (f : K) := hf
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  let D : Divisor k K := Finsupp.mapRange (fun z : ℤ => z / (q : ℤ)) (by simp) (divisor (f : K))
  have hD : divisor (f : K) = q • D := by
    ext w
    simp only [D, Finsupp.smul_apply, Finsupp.mapRange_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel', divisor_apply]
    rw [divisor_apply]
    exact hf' w
  have hdegD : Divisor.deg D = 0 := by
    have h0 := Divisor.deg_divisor (k := k) (f : K)
    rw [hD, map_nsmul, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hq
    · exact h
  have hri := hγ (D + E)
  rw [map_add (f := _), hdegD, zero_add] at hri
  have hn : γ < (n : ℤ) := by
    dsimp [n]
    by_cases h : 0 ≤ γ
    · rw [Int.toNat_of_nonneg h]
      omega
    · have : (0 : ℤ) ≤ (γ.toNat : ℤ) := by positivity
      omega
  have hpos : 0 < Module.finrank k (D + E).L := by omega
  obtain ⟨⟨h, hmem⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hh : h ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hle := (Divisor.mem_L_iff_le hh).mp hmem
  let u : Kˣ := Units.mk0 h hh
  have hval : ((f * u ^ q : Kˣ) : K) = (f : K) * h ^ q := by simp [u]
  have hgne : ((f * u ^ q : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hgdiv : divisor ((f * u ^ q : Kˣ) : K) = q • (D + divisor h) := by
    rw [hval, divisor_mul f.ne_zero (pow_ne_zero _ hh), UpperTheory.exists_finite_span_kummerSelmer_representatives.divisor_pow' hh, hD, smul_add]
  have hgV : ((f * u ^ q : Kˣ) : K) ∈ V := by
    rw [hV, Divisor.mem_L_iff_le hgne, hgdiv, ← smul_add]
    have h3 : D + divisor h + E = divisor h + (D + E) := by abel
    rw [h3]
    exact nsmul_nonneg hle q
  refine ⟨f * u ^ q, ?_, ?_, u⁻¹, by group⟩
  · intro w
    rw [← divisor_apply, hgdiv, Finsupp.smul_apply, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  · refine ⟨fun i => b.repr ⟨_, hgV⟩ i, ?_⟩
    have hs := b.sum_repr ⟨_, hgV⟩
    have hs' := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hs'
    exact hs'.symm
