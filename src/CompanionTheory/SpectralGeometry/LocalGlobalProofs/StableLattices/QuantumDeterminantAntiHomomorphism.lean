module

public import Formalism.PeriodIntegrals.QmDefs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.DoubleRowIncreasing
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem anti_list_prod {A B : Type} [Ring A] [Ring B] (f : A → B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) (l : List A) :
    f l.prod = (l.map f).reverse.prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih => simp [List.prod_cons, hm, ih]

theorem anti_Tm {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    {m : ℕ} (E : Fin m → Fin m → A) (v : ℂ) (a b : Fin m) :
    f (Tm E v a b) = Tm (fun a b => f (E b a)) v b a := by
  have hal : f (algebraMap ℂ A v) = algebraMap ℂ B v := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, h1]
  unfold Tm
  by_cases h : a = b
  · subst h; simp [hal]
  · simp [h, Ne.symm h]

theorem qdet_eq_qminorRow_rev {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E)
    (u : ℂ) : qdet E u = PI.qminorRow E (id ∘ Fin.revPerm) (id ∘ Fin.revPerm) u := by
  have hrow : PI.RowForm := quantum_minor_row_form
  rw [← hrow A m m E hE, quantumMinorRowSkew_holds A m m E id _ Fin.revPerm u,
    quantumMinorColSkew_holds A m m E hE id id Fin.revPerm u, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rfl

theorem qdet_anti {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B) (h1 : f 1 = 1)
    (hm : ∀ x y, f (x * y) = f y * f x) {m : ℕ} (E : Fin m → Fin m → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  rw [qdet_eq_qminorRow_rev E hE]
  unfold qdet qminor PI.qminorRow

  rw [map_sum]
  refine (Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmRowForm.revConj m) _ _ (fun σ => ?_)).symm
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, PI.UnitaryGroupMassFormula.QmRowForm.sign_revConj,
    anti_list_prod f h1 hm, List.map_ofFn, PI.UnitaryGroupMassFormula.QmRowForm.reverse_ofFn']
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => ?_)
  simp only [Function.comp_apply, anti_Tm f h1, id]
  show Tm _ _ _ _ = Tm _ _ (Fin.revPerm (σ (Fin.revPerm k))) _
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  rw [Nat.cast_sub (by omega : (k : ℕ) + 1 ≤ m)]
  push_cast
  ring

end GlobalTheory.CompanionTheory.RgTransport
