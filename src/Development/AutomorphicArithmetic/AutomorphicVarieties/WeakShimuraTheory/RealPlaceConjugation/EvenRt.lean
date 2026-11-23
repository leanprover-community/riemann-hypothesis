module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CcConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.residualCharacter_complexConjugation_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (σ : G T.F Ω), IsCC σ → ∀ w ∈ [0, wPs, -wPs], T.rbU w σ = 1 := by
  intro Ω _ _ _ l _ c D hD T σ hσ w hw
  have hτ : IsCC (resQ T.F σ) := by
    unfold IsCC at *
    exact hσ
  have hconj := isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC
  have hP : D.Psi (resQ T.F σ) = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hconj
    rw [← hD.Psi_even, ← hu]
    simp only [map_mul, map_inv]
    rw [mul_comm, inv_mul_cancel_left]
  have hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ) := by
    have : D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ) := by
      unfold Raw.th
      rfl
    rw [MonoidHom.mul_apply, hP, mul_one] at this
    exact this
  have hrt : (T.fr ∅).rt w σ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
  show (Units.map _) ((T.fr ∅).rt w σ) = 1
  rw [hrt, map_one]
