module

public import Mathlib.FieldTheory.Perfect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_perfectPart_algHom : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
    ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  intro p _ k _ _ _ A _ _ _
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨AlgHom.id k A, fun a => ⟨1, Subsingleton.elim _ _⟩, fun a => ⟨a, Subsingleton.elim _ _⟩⟩
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical A
  set N := nilradical A with hNdef
  set q := p ^ (n + 1) with hqdef
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : ∀ x : A, x ∈ N → x ^ q = 0 := by
    intro x hx
    have h1 : x ^ n ∈ N ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    have hle : n ≤ q := by
      have := Nat.lt_pow_self (n := n + 1) hp1
      omega
    rw [← Nat.sub_add_cancel hle, pow_add, h1, mul_zero]
  haveI : Module.Finite k (A ⧸ N) := Module.Finite.trans A (A ⧸ N)
  haveI : IsReduced (A ⧸ N) := (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  have hroot : ∀ m : ℕ, ∀ a : A ⧸ N, ∃ b, a = b ^ p ^ m := by
    intro m
    induction m with
    | zero => intro a; exact ⟨a, by simp⟩
    | succ m ih =>
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨c, hc⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (A ⧸ N) b
      exact ⟨c, by rw [hb, hc, ← pow_mul, ← pow_succ']⟩
  have hlift : ∀ a : A, ∃ b : A, a - b ^ q ∈ N := by
    intro a
    obtain ⟨c, hc⟩ := hroot (n + 1) (Ideal.Quotient.mk N a)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, ?_⟩
    rw [← Ideal.Quotient.eq, map_pow]
    exact hc
  have hu : ∀ a b c : A, a - b ^ q ∈ N → a - c ^ q ∈ N → b ^ q = c ^ q := by
    intro a b c hb hc
    have h1 : (b - c) ^ q ∈ N := by
      rw [hqdef, sub_pow_char_pow]
      have : b ^ p ^ (n + 1) - c ^ p ^ (n + 1) = (a - c ^ q) - (a - b ^ q) := by ring
      rw [this]
      exact N.sub_mem hc hb
    have h2 : b - c ∈ N := mem_nilradical.mpr (IsNilpotent.of_pow (mem_nilradical.mp h1))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3
  choose β hβ using hlift
  have hf : ∀ a c : A, a - c ^ q ∈ N → β a ^ q = c ^ q := fun a c hc => hu a _ _ (hβ a) hc
  let π : A →ₐ[k] A :=
    { toFun := fun a => β a ^ q
      map_one' := by
        rw [hf 1 1 (by simp), one_pow]
      map_mul' := fun x y => by
        rw [hf (x * y) (β x * β y) ?_, mul_pow]
        have : x * y - (β x * β y) ^ q = x * (y - β y ^ q) + (x - β x ^ q) * β y ^ q := by ring
        rw [this]
        exact N.add_mem (N.mul_mem_left _ (hβ y)) (N.mul_mem_right _ (hβ x))
      map_zero' := by
        rw [hf 0 0 (by rw [zero_pow (by positivity), sub_zero]; exact N.zero_mem), zero_pow (by positivity)]
      map_add' := fun x y => by
        rw [hf (x + y) (β x + β y) ?_, hqdef, add_pow_char_pow]
        rw [hqdef, add_pow_char_pow]
        have : x + y - (β x ^ p ^ (n + 1) + β y ^ p ^ (n + 1)) =
            (x - β x ^ q) + (y - β y ^ q) := by rw [hqdef]; ring
        rw [this]
        exact N.add_mem (hβ x) (hβ y)
      commutes' := fun c => by
        set d := (iterateFrobeniusEquiv k p (n + 1)).symm c with hd
        have hdc : d ^ q = c := by
          have h0 := RingEquiv.apply_symm_apply (iterateFrobeniusEquiv k p (n + 1)) c
          rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at h0
          rw [hqdef, hd]
          exact h0
        rw [hf _ (algebraMap k A d) ?_, ← map_pow, hdc]
        rw [← map_pow, hdc, sub_self]
        exact N.zero_mem }
  have hπ : ∀ a, π a = β a ^ q := fun a => rfl
  refine ⟨π, fun a => ?_, fun a => ⟨β a ^ p ^ n, ?_⟩⟩
  · rw [hπ]
    exact mem_nilradical.mp (hβ a)
  · rw [map_pow, ← pow_mul, ← pow_succ, hπ a]
    have h2 : β a - π (β a) ∈ N := mem_nilradical.mpr (by rw [hπ]; exact mem_nilradical.mp (hβ _))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3

end GlobalTheory
