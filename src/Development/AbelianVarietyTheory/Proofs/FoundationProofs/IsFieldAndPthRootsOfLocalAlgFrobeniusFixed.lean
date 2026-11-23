module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.LocalRing.Defs
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
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

namespace GlobalTheory

theorem localAlg_frob_fixed_isField_and_pth_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  intro p hp k A _ _ _ _ _ T f hf hT hfix
  have hp1 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt

  have hint : ∀ t ∈ (T : Set A), IsIntegral k t := by
    intro t ht
    refine ⟨Polynomial.X ^ (p ^ f) - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp1)
    · simp [hfix t ht]
  have hfinA : Module.Finite k (Algebra.adjoin k (T : Set A)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet hint
  rw [hT] at hfinA
  haveI : Module.Finite k A := Module.Finite.equiv (Subalgebra.topEquiv (R := k) (A := A)).toLinearEquiv

  have hpk : ((p ^ f : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]; exact dvd_pow_self p hf.ne'
  have hD : KaehlerDifferential.D k A = 0 := by
    apply Derivation.ext_of_adjoin_eq_top (T : Set A) hT
    intro t ht
    have h1 := (KaehlerDifferential.D k A).leibniz_pow t (p ^ f)
    rw [hfix t ht] at h1
    rw [h1, ← Nat.cast_smul_eq_nsmul k, hpk, zero_smul]
    rfl
  haveI : Subsingleton (Ω[A⁄k]) := by
    constructor
    intro x y
    have hx : ∀ z : Ω[A⁄k], z = 0 := by
      intro z
      have htop := KaehlerDifferential.span_range_derivation k A
      have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by rw [htop]; trivial
      rw [hD] at hz
      have : Set.range (⇑(0 : Derivation k A (Ω[A⁄k]))) ⊆ ({0} : Set (Ω[A⁄k])) := by
        rintro _ ⟨w, rfl⟩; simp
      have := Submodule.span_mono (R := A) this hz
      simpa using this
    rw [hx x, hx y]
  haveI : Algebra.FormallyUnramified k A := ⟨inferInstance⟩
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hField : IsField A := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  refine ⟨hField, ?_⟩
  intro y a hy
  letI : Field A := hField.toField
  haveI : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A
  haveI : ExpChar k p := ExpChar.prime hp.out
  have hmem : y ∈ perfectClosure k A := by
    rw [mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, by rw [pow_one, hy]; exact ⟨a, rfl⟩⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

end GlobalTheory
