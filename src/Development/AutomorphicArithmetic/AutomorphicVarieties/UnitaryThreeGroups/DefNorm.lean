module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
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

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.isDeform_normalised_iff :
    ∀ {G C : Type} [Group G] [CommRing C] (r r' : G →* GG (m := 3) (R := C))
      (γ : G → Matrix (Fin 3) (Fin 3) C) (c g₁ : G),
      Normalised c g₁ r → IsDeform r γ r' → (Normalised c g₁ r' ↔ NormCoc c g₁ r γ) := by
  intro G C _ _ r r' γ c g₁ hn hd
  have hc : (r' c).mat = 1 + γ c := by rw [(hd c).2, hn.atc, Matrix.mul_one]
  have hz : zmat c g₁ r' = zmat c g₁ r + zvar c g₁ r γ := by
    simp only [zmat, zvar, (hd _).2, Matrix.add_mul, Matrix.one_mul]
    abel
  have h12 : zmat c g₁ r' 0 1 = zvar c g₁ r γ 0 1 := by
    rw [hz, Matrix.add_apply, hn.z12, zero_add]
  have h21 : zmat c g₁ r' 1 0 = zvar c g₁ r γ 1 0 := by
    rw [hz, Matrix.add_apply, hn.z21, zero_add]
  constructor
  · intro h
    refine ⟨?_, h12 ▸ h.z12, h21 ▸ h.z21⟩
    have := h.atc
    rw [hc] at this
    exact add_eq_left.mp this
  · intro h
    exact ⟨by rw [hc, h.atc, add_zero], h12.trans h.z12, h21.trans h.z21⟩
