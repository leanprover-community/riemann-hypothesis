module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

section

variable {Γ k : Type} [Group Γ] [Field k]

private theorem dg_val {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = Matrix.diagonal fun i => (a i g : k) := rfl

private theorem ss_dg_one (b : Fin 1 → Γ →* kˣ) : IsSSRep (dg b) := by
  have key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W := by
    intro W g v hv
    have : ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v := by
      ext i
      fin_cases i
      simp [dg_val, Matrix.mulVec_diagonal]
    rw [this]
    exact W.smul_mem _ hv
  intro W _
  obtain ⟨W', hW'⟩ := exists_isCompl W
  exact ⟨W', key W', hW'⟩

private theorem dg_succ {t : ℕ} (a : Fin (t + 1) → Γ →* kˣ) :
    dg a = sumRep (dg fun i : Fin t => a i.castSucc) (dg fun _ : Fin 1 => a (Fin.last t)) := by
  ext g : 1
  apply Units.ext
  rw [GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

private theorem ss_dg {t : ℕ} (a : Fin t → Γ →* kˣ) : IsSSRep (dg a) := by
  induction t with
  | zero => exact GlobalTheory.BCGal.ss_zero _
  | succ t ih =>
    rw [dg_succ]
    exact GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)

end

theorem dgFacts_holds : DgFacts := by
  intro Γ k _ _ t a
  refine ⟨ss_dg a, fun g => ?_⟩
  show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _
  rw [dg_val, Matrix.charpoly_diagonal]

end UpperTheory.Gal.TP.Sub

end
