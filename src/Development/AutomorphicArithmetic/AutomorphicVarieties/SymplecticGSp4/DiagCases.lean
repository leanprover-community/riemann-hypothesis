module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ContentBoundLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.diagCases :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoV Ω l → ∀ r, D.EPt r → DiagType r → ((∀ s ∈ D.Ip l, r s 0 0 = ((D.th s : c.O) : PadicAlgCl l)) ∧ ∀ i j, (wt i j).2 < 0 → ¬ Ge r i j) ∨ ((∀ s ∈ D.Ip l, r s 0 0 = ((D.al s : c.O) : PadicAlgCl l)) ∧ ∀ i j, 0 < (wt i j).2 → ¬ Ge r i j) := by
  intro Ω _ _ _ l _ c D hD hS r hr hT
  obtain ⟨κ, m, -, hm, hdiag, -⟩ := diagChar D hD r hr hT
  rcases hm with rfl | rfl
  · left
    refine ⟨fun s hs => ?_, fun i j hij hG => ?_⟩
    · simpa [Raw.ps] using hdiag 0 s hs
    · have hne : i ≠ j := by
        rintro rfl
        simp [wt] at hij
      have hlt := diagonal_character_order_lt_of_stable_flag D hD hS r hr hT id Function.injective_id hdiag i j hne hG
      revert hij hlt
      fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]
  · right
    refine ⟨fun s hs => ?_, fun i j hij hG => ?_⟩
    · simpa [Raw.ps] using hdiag 0 s hs
    · have hne : i ≠ j := by
        rintro rfl
        simp [wt] at hij
      have hinj : Function.Injective (![2, 3, 0, 1] : Fin 4 → Fin 4) := by decide
      have hlt := diagonal_character_order_lt_of_stable_flag D hD hS r hr hT _ hinj hdiag i j hne hG
      revert hij hlt
      fin_cases i <;> fin_cases j <;> simp [wt, muW, lamW]
