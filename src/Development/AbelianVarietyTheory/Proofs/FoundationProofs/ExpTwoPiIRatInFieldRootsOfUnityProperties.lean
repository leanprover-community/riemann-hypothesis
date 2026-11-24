module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRoots

theorem alg_mem_range (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : z ∈ ε.range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hi : IsIntegral ℚ z := hz.isIntegral
  set p := minpoly ℚ z with hp
  have hm : p.Monic := minpoly.monic hi
  have hqm : (p.map (algebraMap ℚ Ω)).Monic := hm.map _
  have hroots := hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree
  have hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  rw [Polynomial.map_map, hcomp] at hroots
  have hne : p.map (algebraMap ℚ ℂ) ≠ 0 := (hm.map _).ne_zero
  have hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ z
  rw [← hroots] at hzr
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hzr
  exact ⟨w, hw⟩

theorem exp_isAlgebraic (x : ℚ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) := by
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ) := by
        exact_mod_cast (Rat.num_div_den x).symm
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_nz
      rw [hx]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩
  simp [hpow]

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  intro Ω _ _ _ ε
  have hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range :=
    fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)
  have he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    intro x
    obtain ⟨w, hw⟩ := hr x
    exact Function.invFun_eq ⟨w, hw⟩
  have hinj : Function.Injective ε := ε.injective
  refine ⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩
  · apply hinj; rw [he, map_one]; simp
  · intro x y; apply hinj
    rw [map_mul, he, he, he, ← Complex.exp_add]; congr 1; push_cast; ring
  · intro N hN
    apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj
    rw [he]
    have h := Complex.isPrimitiveRoot_exp N hN.ne'
    convert h using 2
    push_cast; ring

end GlobalTheory.FNRoots
