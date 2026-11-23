module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGen
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

theorem finOrdExists_of (hΦ : DVR.PhiFunStatement) (hP : PhiPowStatement) : FinOrdExistsStatement := by
  intro V _ _ _ D F _ _ _ k hk p w hw
  obtain ⟨Φ, hΦr⟩ := hΦ V (maximalIdeal V) D F k hk p w hw
  obtain ⟨c, hc, hcp⟩ := hP V (maximalIdeal V) D F k hk p w hw
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (c⁻¹) (by omega : 0 < k)
  have hζc : ζ ^ k * c = 1 := by rw [hζ, inv_mul_cancel₀ hc]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_mul] at hζc
    exact zero_ne_one hζc
  refine ⟨ζ, hζ0, k, hk, ?_⟩
  intro ss ts h

  have hpow : (Φ ^ k) (ss 0) = c • ss 0 := by
    have := hcp (fun i => (Φ ^ (i : ℕ)) (ss 0)) (by
      intro i
      rw [hΦr]
      simp only [Fin.val_succ, Fin.coe_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at this
    simpa using this
  have key : ∀ n : ℕ, (hn : n ≤ k) → ss ⟨n, by omega⟩ = ζ ^ n • (Φ ^ n) (ss 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := h ⟨n, by omega⟩
      rw [hΦr] at h1
      rw [isSmul_iff] at h2
      have e : ss ⟨n + 1, by omega⟩ = ss (Fin.succ ⟨n, by omega⟩) := rfl
      have e0 : ss ⟨n, by omega⟩ = ss (Fin.castSucc ⟨n, by omega⟩) := rfl
      rw [e, h2, h1, ← e0, ih (by omega), LinearMap.map_smul, smul_smul, pow_succ' ζ n, pow_succ' Φ n,
        Module.End.mul_apply]
  have hlast : ss (Fin.last k) = ss 0 := by
    have := key k le_rfl
    have e : ss (Fin.last k) = ss ⟨k, by omega⟩ := rfl
    rw [e, this, hpow, smul_smul, hζc, one_smul]
  intro α j
  rw [hlast]

end ReciprocityTheory.ChartRestriction.G.H1
