module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.MulVecMemHeadColsU
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.ThetaMbeU
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open scoped Matrix

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {r : ℕ}

theorem head_map {Z : M.Mat (r + 1)} {Y : M.Mat r} (hY : ∀ a b : Fin r, Y.Z a b = Z.Z a.castSucc b.castSucc) :
    (Z.Z.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc = Y.Z.map M.R.subtype := by
  ext a b
  simp [hY]

theorem det_eq_ellU_b {Z : M.Mat (r + 1)} {Y : M.Mat r} {al : Fin r → M.R}
    (hY : ∀ a b : Fin r, Y.Z a b = Z.Z a.castSucc b.castSucc)
    (hal : ∀ a : Fin r, al a = Z.Z (Fin.last r) a.castSucc) :
    (Z.Z.map M.R.subtype).det = (Y.Z.map M.R.subtype).det * ellU hY hal (bCls Z.Z) := by
  rw [det_schur _ (by rw [head_map hY]; exact Y.unit), head_map hY, bCls, ellU_mk, lamE_apply]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.map_apply, hal]
  rfl

theorem mbeU_holds (M : Model F E) (r : ℕ) : MbeU M r := by
  intro Z₁ Z₂ Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb hdet
  have hY₁ : ∀ a b : Fin r, Y₁.Z a b = Z₁.Z a.castSucc b.castSucc := fun a b => (hY a b).1
  have hY₂ : ∀ a b : Fin r, Y₂.Z a b = Z₂.Z a.castSucc b.castSucc := fun a b => (hY a b).2
  have hbe₁ : ∀ a : Fin r, be₁ a = Z₁.Z a.castSucc (Fin.last r) := fun a => (hb a).1
  have hbe₂ : ∀ a : Fin r, be₂ a = Z₂.Z a.castSucc (Fin.last r) := fun a => (hb a).2.1
  have hal₁ : ∀ a : Fin r, al₁ a = Z₁.Z (Fin.last r) a.castSucc := fun a => (hb a).2.2.1
  have hal₂ : ∀ a : Fin r, al₂ a = Z₂.Z (Fin.last r) a.castSucc := fun a => (hb a).2.2.2
  have hζ : ellU hY₁ hal₁ (bCls Z₁.Z) = ellU hY₂ hal₂ (bCls Z₂.Z) := by
    have h := hdet
    rw [headDet, headDet, head_map hY₁, head_map hY₂, det_eq_ellU_b hY₁ hal₁, det_eq_ellU_b hY₂ hal₂] at h
    have u₁ := Y₁.unit
    have u₂ := Y₂.unit
    have h' : ((Y₁.Z.map M.R.subtype).det * (Y₂.Z.map M.R.subtype).det) * ellU hY₂ hal₂ (bCls Z₂.Z) =
        ((Y₁.Z.map M.R.subtype).det * (Y₂.Z.map M.R.subtype).det) * ellU hY₁ hal₁ (bCls Z₁.Z) := by
      linear_combination h
    exact ((u₁.mul u₂).mul_left_cancel h').symm
  rw [Model.nIsoBA]
  exact Nat.card_congr (isoEquivU hY₁ hal₁ hY₂ hal₂ hbe₁ hbe₂ hζ)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL
