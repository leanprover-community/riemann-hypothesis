module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAaVector
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem ly_Eab_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) (s : Matrix (Fin n) (Fin n) ℂ) :
    EabH H a b (fun x => F (s * x)) = fun x => EabH H a b F (s * x) := by
  funext x
  simp only [EabH, RdV, Matrix.mul_assoc]

theorem ly_Top_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.QuantumDeterminants.Top (EabH H) v a b (fun x => F (s * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) v a b F (s * x) := by
  funext x
  simp only [Formalism.QuantumDeterminants.Top, EabH, RdV, Matrix.mul_assoc]

theorem ly_foldr_comm {X E : Type*} (L : (X → E) → (X → E)) (l : List ((X → E) → (X → E)))
    (hl : ∀ T ∈ l, ∀ f, T (L f) = L (T f)) (f : X → E) :
    l.foldr (fun T h => T h) (L f) = L (l.foldr (fun T h => T h) f) := by
  induction l with
  | nil => rfl
  | cons T l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun T' hT' => hl T' (by simp [hT'])), hl T (by simp)]

theorem ly_qminor_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H : Matrix (Fin n) (Fin n) ℂ) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (F : Matrix (Fin n) (Fin n) ℂ → E)
    (s x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) a b u (fun y => F (s * y)) x = qminorOp (EabH H) a b u F (s * x) := by
  unfold qminorOp
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply]
  congr 1
  rw [ly_foldr_comm (fun f y => f (s * y)) _ ?_ F]
  intro T hT f
  simp only [List.mem_ofFn, Set.mem_range] at hT
  obtain ⟨i, rfl⟩ := hT
  exact ly_Top_left H _ _ _ f s

theorem left_aa : LeftAA := by
  unfold LeftAA
  intro E _ _ k r z m hm u ell F s g hs hg
  constructor
  · simp only [AAop]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [ly_qminor_left, coef_left_aa k r z m hm s g c hs]
  · simp only [AAvop]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [ly_qminor_left, coef_left_aa_vector k r z m hm s g B hs hg]

end AAInvW
