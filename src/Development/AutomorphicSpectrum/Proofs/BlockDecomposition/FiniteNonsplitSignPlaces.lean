module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.FinSign

theorem ordL_eq_zero_of_v_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (h : Valued.v x = 1) : ordL x = 0 := by
  unfold ordL
  rw [dite_eq_right (by rw [h]; exact one_ne_zero)]
  simp [h]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := by
  intro E _ _ _ hU n γ₀ H₀ _ _ hpos P₁
  obtain ⟨hd0, -⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine (GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 _ hd0)).subset ?_
  rintro w ⟨hw, hs⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0]
  intro h1
  apply hs
  unfold sgnOn
  have hv : Valued.v (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H₀
        (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))).det) = 1 :=
    (w.valuedAdicCompletion_eq_valuation' _).trans h1
  rw [aeval_map_mat, GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁), ordL_eq_zero_of_v_eq_one hv]
  simp

end GlobalTheory.CompanionTheory.FinSign
