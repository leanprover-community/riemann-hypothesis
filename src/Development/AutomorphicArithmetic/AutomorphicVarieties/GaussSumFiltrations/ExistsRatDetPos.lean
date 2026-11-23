module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible

@[expose] public section

open NumberField GlobalTheory.BorelCoh UpperTheory.V.TR
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.WeakApproxGL

theorem denseRange_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange ((pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F))) := by
  have hc : Continuous (infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

theorem exists_rat_det_pos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ)
    (g : GL (Fin a) (InfinitePlace F → ℝ)), ∃ h : GL (Fin a) F, ∀ v, 0 < ((((Matrix.GeneralLinearGroup.map (pInf F)).comp
      (GlobalTheory.CuspRep.ratGL F a)) h) * g).val.det v := by
  intro F _ _ _ a g
  set φ : F →+* (InfinitePlace F → ℝ) := (pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F)) with hφ
  have hcomp : ∀ h : GL (Fin a) F, (((Matrix.GeneralLinearGroup.map (pInf F)).comp (GlobalTheory.CuspRep.ratGL F a)) h).val
      = (h.val).map φ := fun h => by
    ext i j; rfl
  have hdu : IsUnit g.val.det := Matrix.isUnits_det_units g
  have hd : ∀ v, g.val.det v ≠ 0 := fun v => ((Pi.isUnit_iff.1 hdu) v).ne_zero
  have hopen : IsOpen {y : InfinitePlace F → ℝ | ∀ v, 0 < y v * g.val.det v} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  obtain ⟨t, ht⟩ := (denseRange_inf F).exists_mem_open hopen
    ⟨fun v => (g.val.det v)⁻¹, fun v => by simp [hd v]⟩
  have ht' : ∀ v, 0 < φ t v * g.val.det v := ht
  cases a with
  | zero =>
    refine ⟨1, fun v => ?_⟩
    rw [Matrix.det_isEmpty]
    exact one_pos
  | succ n =>
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have := ht' v
      simp at this
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.diagonal (Function.update 1 0 t)
    have hD : D.det = t := by
      rw [Matrix.det_diagonal, Fin.prod_univ_succ]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (hD ▸ ht0), fun v => ?_⟩
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
    rw [Units.val_mul, Matrix.det_mul, hcomp, e, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hD]
    exact ht' v

end GlobalTheory.WeakApproxGL
