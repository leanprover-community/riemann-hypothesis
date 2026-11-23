module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations

@[expose] public section

open NumberField

namespace GlobalTheory.ColonPowCancel

theorem exists_inv {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) : ∃ 𝔠 : Submodule (𝓞 K) K, 𝔠 * 𝔟 = 1 := by
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ⟨𝔟, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply h0
    have : (I : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by rw [h]
    rw [FractionalIdeal.coe_zero] at this
    exact this
  refine ⟨((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K), ?_⟩
  have h1 : I⁻¹ * I = 1 := inv_mul_cancel₀ hI
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K => (J : Submodule (𝓞 K) K)) h1
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at h2
  exact h2

theorem mem_colon_iff {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    (N A : Submodule R K) (r : R) :
    r ∈ N.colon (A : Set K) ↔ Submodule.span R {algebraMap R K r} * A ≤ N := by
  rw [Submodule.mem_colon]
  constructor
  · intro h
    rw [Submodule.mul_le]
    intro m hm a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc, ← Algebra.smul_def]
    exact N.smul_mem c (h a ha)
  · intro h a ha
    rw [Algebra.smul_def]
    exact h (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) ha)

theorem colon_pow_mul_cancel {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K)
    (hfg : 𝔟.FG) (h0 : 𝔟 ≠ ⊥) (p : ℕ) (A N : Submodule (𝓞 K) K) :
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  obtain ⟨𝔠, hc⟩ := exists_inv 𝔟 hfg h0
  have hp : 𝔠 ^ p * 𝔟 ^ p = 1 := by rw [← mul_pow, hc, one_pow]
  ext r
  rw [mem_colon_iff, mem_colon_iff, mul_left_comm]
  constructor
  · intro h
    have h' : 𝔠 ^ p * (𝔟 ^ p * (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r} * A))
        ≤ 𝔠 ^ p * (𝔟 ^ p * N) := by gcongr
    rwa [← mul_assoc, ← mul_assoc (𝔠 ^ p), hp, one_mul, one_mul] at h'
  · intro h
    gcongr

end GlobalTheory.ColonPowCancel
