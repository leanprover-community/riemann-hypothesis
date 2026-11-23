module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
