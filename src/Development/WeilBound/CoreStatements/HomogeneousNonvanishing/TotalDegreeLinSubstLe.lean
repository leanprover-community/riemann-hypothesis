module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Mathlib.Algebra.MvPolynomial.Nilpotent

@[expose] public section

set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

private theorem totalDegree_aeval_le_of_totalDegree_le_one {K : Type} [Field K] {σ τ : Type} (L : σ → MvPolynomial τ K)
    (hL : ∀ i, (L i).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (aeval L f).totalDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]

  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans (le_trans ?_ (le_totalDegree hs))
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans ?_
  calc s i * (L i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hL i)
    _ = s i := mul_one _

theorem PositivityTheory.UnitarySelfGeneration.UnitProductCombination.totalDegree_linSubst_le {K : Type} [Field K] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) K)
    (f : MvPolynomial (Fin B × Fin N) K) : (linSubst M f).totalDegree ≤ f.totalDegree := by
  unfold linSubst
  refine totalDegree_aeval_le_of_totalDegree_le_one _ (fun p => ?_) f
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X _).le

private theorem linSubst_linSubst' {K : Type} [Field K] {B N n m : ℕ} (M : Matrix (Fin N) (Fin n) K)
    (P : Matrix (Fin n) (Fin m) K) (f : MvPolynomial (Fin B × Fin N) K) :
    linSubst P (linSubst M f) = linSubst (M * P) f := by
  unfold linSubst
  rw [← AlgHom.comp_apply, comp_aeval]
  apply congrArg (fun g : Fin B × Fin N → MvPolynomial (Fin B × Fin m) K => aeval g f)
  funext p
  simp only [map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem linSubst_one' {K : Type} [Field K] {B N : ℕ} (f : MvPolynomial (Fin B × Fin N) K) :
    linSubst (1 : Matrix (Fin N) (Fin N) K) f = f := by
  unfold linSubst
  have e : (fun p : Fin B × Fin N => ∑ k, C ((1 : Matrix (Fin N) (Fin N) K) p.2 k) * X (p.1, k)) = X := by
    funext p
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro k _ hk
      rw [Matrix.one_apply_ne (Ne.symm hk), C_0, zero_mul]
    · simp
  rw [e, aeval_X_left_apply]

private theorem linSubst_mul' {K : Type} [Field K] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) K)
    (a b : MvPolynomial (Fin B × Fin N) K) : linSubst M (a * b) = linSubst M a * linSubst M b := by
  unfold linSubst
  exact map_mul _ _ _

private theorem linSubst_zero {K : Type} [Field K] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) K) :
    linSubst M (0 : MvPolynomial (Fin B × Fin N) K) = 0 := by
  unfold linSubst
  exact map_zero _

theorem PositivityTheory.UnitarySelfGeneration.UnitProductCombination.irreducible_linSubst {K : Type} [Field K] {B N n : ℕ} {M : Matrix (Fin N) (Fin n) K}
    {P : Matrix (Fin n) (Fin N) K} (h : M * P = 1) {f : MvPolynomial (Fin B × Fin N) K} (hf : Irreducible f) :
    Irreducible (linSubst M f) := by
  have key : ∀ q : MvPolynomial (Fin B × Fin N) K, linSubst P (linSubst M q) = q := fun q => by
    rw [linSubst_linSubst', h, linSubst_one']
  have hdeg : ∀ q : MvPolynomial (Fin B × Fin N) K, (linSubst M q).totalDegree = q.totalDegree := fun q =>
    le_antisymm (PositivityTheory.UnitarySelfGeneration.UnitProductCombination.totalDegree_linSubst_le M q)
      (calc q.totalDegree = (linSubst P (linSubst M q)).totalDegree := by rw [key q]
        _ ≤ _ := PositivityTheory.UnitarySelfGeneration.UnitProductCombination.totalDegree_linSubst_le P _)
  have hu0 : ∀ {σ : Type} (u : MvPolynomial σ K), IsUnit u → u.totalDegree = 0 := by
    intro σ u hu
    obtain ⟨r, -, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    exact totalDegree_C r
  have hunit : ∀ {σ : Type} (q : MvPolynomial σ K), q ≠ 0 → q.totalDegree = 0 → IsUnit q := by
    intro σ q hq hd
    rw [totalDegree_eq_zero_iff_eq_C] at hd
    refine isUnit_iff_eq_C_of_isReduced.mpr ⟨AddMonoidAlgebra.coeff q 0, isUnit_iff_ne_zero.mpr ?_, hd⟩
    intro h0
    apply hq
    rw [hd, h0, C_0]
  have hf0 : f ≠ 0 := hf.ne_zero
  have hMf0 : linSubst M f ≠ 0 := by
    intro h0
    apply hf0
    rw [← key f, h0, linSubst_zero]
  constructor
  · intro hu
    apply hf.not_isUnit
    apply hunit f hf0
    have := hu0 _ hu
    rwa [hdeg] at this
  · intro a b hab
    have hfab : f = linSubst P a * linSubst P b := by rw [← linSubst_mul', ← hab, key]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hMf0 hab
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hMf0 hab
    have hPa0 : linSubst P a ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hfab
      exact hf0 hfab
    have hPb0 : linSubst P b ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfab
      exact hf0 hfab
    have e1 : f.totalDegree = (linSubst P a).totalDegree + (linSubst P b).totalDegree := by
      rw [hfab]
      exact totalDegree_mul_of_isDomain hPa0 hPb0
    have e2 : f.totalDegree = a.totalDegree + b.totalDegree := by
      rw [← hdeg f, hab]
      exact totalDegree_mul_of_isDomain ha0 hb0
    have la := PositivityTheory.UnitarySelfGeneration.UnitProductCombination.totalDegree_linSubst_le P a
    have lb := PositivityTheory.UnitarySelfGeneration.UnitProductCombination.totalDegree_linSubst_le P b
    rcases hf.isUnit_or_isUnit hfab with hPa | hPb
    · left
      apply hunit a ha0
      have := hu0 _ hPa
      omega
    · right
      apply hunit b hb0
      have := hu0 _ hPb
      omega
