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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exp_two_pi_rat_mem_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (r : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero r.den := ⟨r.den_nz⟩
  haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den
  have hζ' : IsPrimitiveRoot (ε ζ) r.den := hζ.map_of_injective ε.injective
  have he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have h1 : ((r.den : ℚ) * r : ℚ) = r.num := Rat.den_mul_eq_num r
    have h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1
    rw [← h2]; ring
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one he
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem Tower.exponent_integral_of_translation_invariant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (hh : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  have e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ) := fun _ _ _ => rfl
  have e10 : ent (ofSL ModularGroup.T) 1 0 = 0 := by rw [e]; simp [ModularGroup.T]
  have e00 : ent (ofSL ModularGroup.T) 0 0 = 1 := by rw [e]; simp [ModularGroup.T]
  have e01 : ent (ofSL ModularGroup.T) 0 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have e11 : ent (ofSL ModularGroup.T) 1 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have key := X.exp_upper _ e10 h r
  rw [hh, e00, e01, e11, mul_one, div_one] at key
  have h1 : eOm ε r = 1 := by
    have : eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r := by rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hr this
  have h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) :=
    Function.invFun_eq (exp_two_pi_rat_mem_range ε r)
  rw [h1, map_one] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2.symm
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = (n : ℂ) := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

end GlobalTheory.KZ
