module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval, Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.Integral\npublic import Mathlib.NumberTheory.GaussSum\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\npublic import Mathlib.NumberTheory.DirichletCharacter.GaussSum\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.KummerEisensteinGalois Finset

namespace GlobalTheory.KummerEisensteinGalois.ChSum

theorem core {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      (if D + w * n₂ * D' = 0 then (M : K) else 0) * (ψ⁻¹ (w * D') * gaussSum ψ e) := by
  have step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D')) := by
    intro a
    let f : ZMod M ≃ ZMod M :=
      { toFun := fun s => w * (s + n₂ * a)
        invFun := fun b => n₁ * b - n₂ * a
        left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw
        right_inv := fun b => by simp only; linear_combination b * hw }
    rw [← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f, Equiv.coe_fn_mk]
    have h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s := by linear_combination (s + n₂ * a) * hw
    have h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D') := by ring
    rw [h1, h2, AddChar.map_add_eq_mul]; ring
  have hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e := by
    rw [← gaussSum_mulShift_of_isPrimitive e hψ]
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm s]
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]
  split_ifs <;> ring

theorem eval {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    (∀ u : (ZMod M)ˣ, D = u * (-n₂) → D' = u * n₁ →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
        (M : K) * ψ⁻¹ (u : ZMod M) * gaussSum ψ e) ∧
    ((¬ ∃ u : (ZMod M)ˣ, D = u * (-n₂) ∧ D' = u * n₁) →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = 0) := by
  rw [core ψ hψ e he n₁ n₂ w D D' hw]
  refine ⟨fun u hD hD' => ?_, fun hno => ?_⟩
  · have h0 : D + w * n₂ * D' = 0 := by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw
    have hl : w * D' = u := by rw [hD']; linear_combination (u : ZMod M) * hw
    rw [if_pos h0, hl]; ring
  · by_cases hc : D + w * n₂ * D' = 0
    · have hnu : ¬ IsUnit (w * D') := by
        rintro ⟨v, hv⟩
        refine hno ⟨v, ?_, ?_⟩
        · rw [hv]; linear_combination hc
        · rw [hv]; linear_combination (-D') * hw
      rw [if_pos hc, MulChar.map_nonunit _ hnu]; ring
    · rw [if_neg hc, zero_mul]

theorem zpow_eq {M : ℕ} [NeZero M] {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) (z : ℤ) :
    ζ ^ z = AddChar.zmodChar M hζ.pow_eq_one (z : ZMod M) := by
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
  rw [AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv z M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

theorem unit_of_not_dvd (p m : ℕ) (hp : p.Prime) (n : ℤ) (h : ¬ (p : ℤ) ∣ n) :
    ∃ w : ZMod (p ^ m), (n : ZMod (p ^ m)) * w = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc : IsCoprime n ((p : ℤ) ^ m) :=
    (((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨(u : ZMod (p ^ m)), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

theorem charSum : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  intro p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn
  have hp : p.Prime := Fact.out
  have he := AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ
  set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def
  have hG : gaussS p m ψ ζm = gaussSum ψ e := rfl
  have hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') =
      e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) := by
    intro a b
    rw [zpow_eq hζ]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hz, hG]
  rw [← Nat.cast_pow]
  by_cases h1 : (p : ℤ) ∣ n₁
  · have h2 : ¬ (p : ℤ) ∣ n₂ := fun h => hn ⟨h1, h⟩
    obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₂ h2
    have hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1 := by rw [neg_mul_neg, hw]
    have key := eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w)
      (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'
    have hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
          e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) =
        ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) *
          e (a * (d' : ZMod (p ^ m)) + b * (d : ZMod (p ^ m))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a =
        (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]
    rw [hswap]
    rw [neg_neg] at key
    exact ⟨fun u hd hd' => key.1 u hd' hd,
      fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩
  · obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₁ h1
    exact eval ψ hψ e he _ _ w _ _ hw

end GlobalTheory.KummerEisensteinGalois.ChSum
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.Integral\npublic import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.BitVec\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UnitPiece

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
theorem sum_antidiag (n : ℕ) (G : ℤ → ℤ → K) :
    ∑ q ∈ (n : ℤ).divisorsAntidiag, G q.1 q.2 =
      ∑ d ∈ n.divisors, (G ((n / d : ℕ) : ℤ) d + G (-((n / d : ℕ) : ℤ)) (-(d : ℤ))) := by
  rw [Int.divisorsAntidiag_natCast, sum_disjUnion, sum_map, sum_map, ← sum_add_distrib]
  exact Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => G a b + G (-(a : ℤ)) (-(b : ℤ)))

theorem coefPos_eq (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) :
    coefPos j M ζ a₁ a₂ n = ∑ q ∈ (n : ℤ).divisorsAntidiag,
      if q.1 ≡ a₁ [ZMOD M] then (q.2.sign : K) * ((q.1 : K) / M) ^ (j - 1) * ζ ^ (a₂ * q.2) else 0 := by
  rw [sum_antidiag n (fun A d => if A ≡ a₁ [ZMOD M] then (d.sign : K) * ((A : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0)]
  unfold coefPos
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0, sub_eq_add_neg]
  congr 1
  · split_ifs <;> simp [-Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]
  · split_ifs <;> simp [neg_div, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

def primeTo (p m : ℕ) [NeZero p] : Finset (ZMod (p ^ m)) := univ.filter fun c => ¬ p ∣ c.val

omit [CharZero K] in
theorem sum_unitSet (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m))
    (H : ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ γ ∈ unitSet p m, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det.val : ℕ) : ZMod (p ^ m)) *
      H ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1)
        ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b := by
  have e : ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * H u a v b =
      ∑ w ∈ primeTo p m ×ˢ ((univ : Finset (ZMod (p ^ m))) ×ˢ (primeTo p m ×ˢ (univ : Finset (ZMod (p ^ m))))),
        ψ (w.1 * w.2.2.2 - w.2.1 * w.2.2.1) * H w.1 w.2.1 w.2.2.1 w.2.2.2 := by
    simp only [sum_product]
  rw [e]
  refine sum_of_injOn (fun γ : GL (Fin 2) (ZMod (p ^ m)) =>
    ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 0 1,
     (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 0, (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) 1 1)) ?_ ?_ ?_ ?_
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  · intro γ hγ
    simpa [unitSet, primeTo] using hγ
  · rintro ⟨u, a, v, b⟩ hw hn
    by_cases hu : IsUnit (u * b - a * v)
    · exfalso
      apply hn
      refine ⟨Matrix.GeneralLinearGroup.mk'' !![u, a; v, b] (by simpa [Matrix.det_fin_two] using hu), ?_, ?_⟩
      · simpa [unitSet, primeTo] using hw
      · simp
    · simp only
      rw [MulChar.map_nonunit _ hu, zero_mul]
  · intro γ _
    simp only [ZMod.natCast_zmod_val, Matrix.det_fin_two]

theorem dvd_val_iff (p m : ℕ) [NeZero p] (hm : 1 ≤ m) (z : ℤ) :
    p ∣ (z : ZMod (p ^ m)).val ↔ (p : ℤ) ∣ z := by
  rw [← Int.natCast_dvd_natCast, ZMod.val_intCast]
  have h : (p : ℤ) ∣ ((p ^ m : ℕ) : ℤ) := by push_cast; exact dvd_pow_self _ (by omega)
  rw [Int.emod_def]
  exact dvd_sub_left (h.mul_right _)

theorem col_sum (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (y₁ y₂ n₁ n₂ d d' : ℤ)
    (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₁ * d)) *
          (ψ⁻¹ (d' : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (y₂ * d')) else 0 := by
  have hp : p.Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : 0 < N * p ^ m := Nat.mul_pos hN (pow_pos hp.pos m)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have hζN : IsPrimitiveRoot (ζ ^ N) (p ^ m) := hζ.pow hpos rfl
  have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self _ (by omega)
  have hunit : ∀ z : ℤ, IsUnit (z : ZMod (p ^ m)) ↔ ¬ (p : ℤ) ∣ z := by
    intro z
    rw [← dvd_val_iff p m hm, ← ZMod.natCast_zmod_val (z : ZMod (p ^ m)), ZMod.isUnit_iff_coprime,
      Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd, ZMod.natCast_zmod_val]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.KummerEisensteinGalois.ChSum.charSum p m K ψ (ζ ^ N) hm hψ hζN n₁ n₂ d d' (fun h => h₁ h.1)
  have e : ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - a * (n₂ : ZMod (p ^ m))) *
        ζ ^ (((N : ℤ) * b.val + (p : ℤ) ^ m * y₂) * d')) * ζ ^ (((N : ℤ) * a.val + (p : ℤ) ^ m * y₁) * d) =
      (∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
        (ζ ^ N) ^ ((a.val : ℤ) * d + (b.val : ℤ) * d')) *
        ((ζ ^ (p ^ m)) ^ (y₁ * d) * (ζ ^ (p ^ m)) ^ (y₂ * d')) := by
    simp only [sum_mul]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm a, mul_assoc, mul_assoc, ← zpow_natCast ζ N, ← zpow_natCast ζ (p ^ m), ← zpow_mul, ← zpow_mul,
      ← zpow_mul, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0, ← zpow_add₀ hζ0]
    congr 2
    push_cast; ring
  rw [e]
  obtain ⟨w, hw⟩ := (hunit n₁).mpr h₁
  split_ifs with hc
  · obtain ⟨hs, -, hd'⟩ := hc
    obtain ⟨v, hv⟩ := (hunit d').mpr hd'
    rw [hdvd] at hs
    push_cast at hs
    rw [← hw, ← hv] at hs
    have hww : ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * w = 1 := w.inv_mul
    rw [c1 (v * w⁻¹) ?_ ?_]
    · have : ψ⁻¹ ((v * w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) = ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (d' : ZMod (p ^ m)) := by
        rw [Units.val_mul, map_mul, ← hw, ← hv, mul_comm]
        congr 1
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [this]; ring
    · rw [Units.val_mul]
      linear_combination ((w⁻¹ : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) * hs - (d : ZMod (p ^ m)) * hww
    · rw [Units.val_mul, ← hw, ← hv]
      linear_combination (-(v : ZMod (p ^ m))) * hww
  · rw [c2, zero_mul]
    rintro ⟨u, hd, hd'⟩
    apply hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hdvd]; push_cast; rw [hd, hd']; ring
    · rw [← hunit, hd]; exact u.isUnit.mul ((hunit n₂).mpr h₂).neg
    · rw [← hunit, hd']; exact u.isUnit.mul ((hunit n₁).mpr h₁)

omit [CharZero K] in
theorem sum_affine (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (u c : ZMod (p ^ m)) (hu : IsUnit u) : ∑ b : ZMod (p ^ m), ψ (u * b + c) = 0 := by
  have hp : p.Prime := Fact.out
  have hne : ψ ≠ 1 := by
    intro h
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hψ
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne hψ
  obtain ⟨w, rfl⟩ := hu
  rw [← MulChar.sum_eq_zero_of_ne_one hne]
  exact Equiv.sum_comp ((Units.mulLeft w).trans (Equiv.addRight c)) ψ

theorem isUnit_of_mem (p m : ℕ) [Fact p.Prime] {u : ZMod (p ^ m)} (hu : u ∈ primeTo p m) : IsUnit u := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.natCast_zmod_val u, ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hu).2).symm).pow_right m

omit [CharZero K] in
theorem sum_zero_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → K) (g : ZMod (p ^ m) → ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u * g v b) = 0 := by
  refine sum_eq_zero fun u _ => ?_
  rw [sum_comm]
  refine sum_eq_zero fun v hv => ?_
  rw [sum_comm]
  refine sum_eq_zero fun b _ => ?_
  rw [← sum_mul, ← zero_mul (f u * g v b), ← sum_affine p m hm ψ hψ (-v) (u * b) (isUnit_of_mem p m hv).neg]
  congr 1
  exact sum_congr rfl fun a _ => by congr 1; ring

omit [CharZero K] in
theorem sum_zero_right (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (ψ : DirichletCharacter K (p ^ m))
    (hψ : ψ.IsPrimitive) (f : ZMod (p ^ m) → ZMod (p ^ m) → K) (g : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m),
      ψ (u * b - a * v) * (f u a * g v) = 0 := by
  refine sum_eq_zero fun u hu => sum_eq_zero fun a _ => sum_eq_zero fun v _ => ?_
  rw [← sum_mul, ← zero_mul (f u a * g v), ← sum_affine p m hm ψ hψ u (-(a * v)) (isUnit_of_mem p m hu)]
  simp only [sub_eq_add_neg]

end GlobalTheory.KummerEisensteinGalois.UnitPiece
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero =====
