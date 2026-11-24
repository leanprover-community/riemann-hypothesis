module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

theorem frA_int_reindex {F : Type} [Field F] (O : ValuationSubring F) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix n n F) (w : m → F) :
    (∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i ∈ O) ↔ ∀ i, (A *ᵥ (w ∘ e.symm)) i ∈ O := by
  have h : ∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i = (A *ᵥ (w ∘ e.symm)) (e i) := by
    intro i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Equiv.symm_symm, Function.comp_apply]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  simp only [h]
  constructor
  · intro H j
    simpa using H (e.symm j)
  · intro H i
    exact H (e i)

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem latCrd_of (hL : LatBasis X p θ (reindex₂ X p Q)) (x : Fin X.B.I.n → TpX X p) :
    x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have hPi : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        (((Q⁻¹ : GL (IdxD D) (FpX X p))) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hP : ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hJ : J1 X p θ = jm1 X.B.I.J θ := rfl
  have hv : ∀ w : Fin X.B.I.n → FpX X p,
      (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (w ∘ (idxEquiv X).symm) =
        ((jm1 X.B.I.J θ)ᵀ *ᵥ w) ∘ (idxEquiv X).symm := by
    intro w
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext i
    simp
  rw [hL x]
  unfold IntVec crd1 crd2
  rw [hPi, frA_int_reindex, ← Matrix.mulVec_mulVec, hP, Matrix.transpose_reindex, frA_int_reindex, hJ, ← hv]
  rfl

end Loc

end MassDataIdxSteps
