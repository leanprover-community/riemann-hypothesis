module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CmDatumCharTwoAdicOrderBounds
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.hostData_of_host :
    ∀ (h : Host) {l : ℕ} [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 1 ≤ e → ∀ ψ ∈ h.X c e, h.R1 l ψ ≤ 2 ^ c2 ψ → HostData l e ψ h.o ∧ XData l ψ h.q := by
  intro h l _ c e hl2 he ψ hψ hR
  have hl : l.Prime := Fact.out
  obtain ⟨hchar, hpar⟩ := (Host.mem_X h).mp hψ
  obtain ⟨-, -, h16, ho, -⟩ := hostIndex h
  have hq : 0 < h.q := Nat.pos_of_neZero h.q
  obtain ⟨-, -, -, -, -, hcond, -, -, -, -, hord⟩ := hostTh1 h _ ψ hchar l hl hl2
  obtain ⟨-, -, -, -, hc⟩ := cmDatum_char_two_adic_order_bounds h _ ψ hchar l hl hl2
  obtain ⟨h12, hTb⟩ := hc hR
  refine ⟨⟨hl2, he, ?_, hpar, ho, ?_, hTb, by omega⟩, hq, hcond, ?_⟩
  · exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16)
  · intro r hr hr2
    exact orderOf_dvd_iff_pow_eq_one.mp (hord r hr hr2)
  · have hl3 : 3 ≤ l := by
      have := hl.two_le
      omega
    have hlq : 0 < l * h.q := Nat.mul_pos (by omega) hq
    have hR1 : h.R1 l ψ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := rfl
    have hX : l * h.q ≤ (l * h.q) ^ 2 := Nat.le_self_pow two_ne_zero _
    have hoX : 1 * (l * h.q) ^ 2 ≤ h.o * (l * h.q) ^ 2 := Nat.mul_le_mul_right _ ho
    have hmain : 2 * (l * h.q) ≤ 16 * h.o * (l * h.q) ^ 2 := by nlinarith
    calc 2 * (l * h.q) * 4 ^ n0 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := Nat.mul_le_mul_right _ hmain
      _ = h.R1 l ψ := hR1.symm
      _ ≤ 2 ^ c2 ψ := hR
