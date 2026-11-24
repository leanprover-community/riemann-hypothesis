module

public import Formalism.DistinguishedUnitIdeals.Statement
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

theorem lam_eq_pow_mul {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ)
    (hs : s < ell) :
    abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t := by
  unfold abelian₂
  rw [← Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t) (Finset.mem_range.mpr hs)]

theorem levelCond_of_sub_pow_smul {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (P : PowerSeries O)
    (H b : ℕ) (k : Kind) (hk : k ≠ Kind.down) (V : Submodule O (Fin r → O))
    (y w : Fin r → PowerSeries O) (m : ℕ)
    (h : LevelCond ϖ P H b k V (C (ϖ ^ m) • y - P ^ H • w)) :
    LevelCond ϖ P H b k V y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N + m, z + C (ϖ ^ N) • w, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, ← hz, smul_sub, smul_comm (P ^ H) (C (ϖ ^ N)) w]
    abel
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    refine ⟨N + m, c, z + C (ϖ ^ N) • w, hc, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, smul_comm (P ^ H) (C (ϖ ^ N)) w, ← add_assoc, ← hz,
      smul_sub]
    abel
  | down => exact absurd rfl hk

theorem levels_mod_const_iff_of_no_down : MNone := by
  intro O _ _ _ ϖ _ ℓ ell r p H b kind V _ _ _ _ hnd y
  constructor
  · intro hII s hs
    obtain ⟨d, k, hd⟩ := hII s hs
    rw [lam_eq_pow_mul p H ell s hs, mul_smul] at hd
    exact levelCond_of_sub_pow_smul ϖ (p s) (H s) (b s) (kind s) (hnd s hs) (V s) y _ k hd
  · intro hNN s hs
    refine ⟨0, 0, ?_⟩
    have h0 : (cst (0 : Fin r → O) : Fin r → PowerSeries O) = 0 := by
      funext i; simp [cst]
    simpa [h0] using hNN s hs

end Formalism.ExponentWindows
