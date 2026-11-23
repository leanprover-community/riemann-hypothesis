module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem pow_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (hl : (l : R) ∈ I) (x : R)
    (hx : x - 1 ∈ I) (k : ℕ) : x ^ (l ^ k) - 1 ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have h1 : x ^ (l ^ k) - 1 ∈ I := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
    rw [pow_succ l k, pow_mul, ← mul_geom_sum, pow_succ I (k + 1)]
    refine Ideal.mul_mem_mul ih ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hl h1 ⊢
    rw [map_sub, map_one, sub_eq_zero] at h1

    rw [map_sum]
    simp only [map_pow (Ideal.Quotient.mk I) (x ^ (l ^ k)), h1, one_pow]
    simpa using hl

theorem UpperTheory.V.Ws.H5.finQuot :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {R : Type} [CommRing R] [IsLocalRing R], ((l : ℕ) : R) ∈ maximalIdeal R → ∀ γ : F.G₀ →* Rˣ, TwCh F γ → ∀ N : ℕ, ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : F.G₀ →* Q) (j : Q →* (R ⧸ maximalIdeal R ^ N)ˣ), IsPGroup l Q ∧ IsOpen (q.ker : Set F.G₀) ∧ Anti F q ∧ j.comp q = pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ := by
  intro l _ F R _ _ hl γ hγ N
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  set χ := pushCh (Ideal.Quotient.mk (maximalIdeal R ^ N)) γ with hχ
  have hval : ∀ g, (χ g : R ⧸ maximalIdeal R ^ N) = Ideal.Quotient.mk (maximalIdeal R ^ N) (γ g : R) := fun g => rfl
  have hlc : IsLocallyConstant fun g => (χ g : R ⧸ maximalIdeal R ^ N) := hγ.cont N
  have hlc' : IsLocallyConstant χ := IsLocallyConstant.desc χ Units.val hlc Units.val_injective
  have hfin : Finite χ.range := hlc'.range_finite.to_subtype
  refine ⟨χ.range, inferInstance, hfin, χ.rangeRestrict, χ.range.subtype, ?_, ?_, ?_, rfl⟩
  · rintro ⟨_, g, rfl⟩
    refine ⟨N, Subtype.ext (Units.ext ?_)⟩
    have h := Ideal.pow_le_pow_right (Nat.le_succ N) (pow_pow_sub_one_mem _ l hl _ (hγ.red g) N)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, map_pow] at h
    simpa [hval] using h
  · rw [MonoidHom.ker_rangeRestrict]
    exact hlc'.isOpen_fiber 1
  · refine hγ.toAnti.mono fun g hg => ?_
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hg
    exact Units.ext (by rw [hval, hg]; simp)
