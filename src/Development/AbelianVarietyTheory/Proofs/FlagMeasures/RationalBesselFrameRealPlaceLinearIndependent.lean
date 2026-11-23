module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.RationalFrame

open NumberField Formalism.L2.SG.PoincareInHH

theorem hJ_lin {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) (c : ℂ) (w : Fin n → ℂ) :
    hJ ε x (∑ i, g i • y i + c • w) = ∑ i, g i * hJ ε x (y i) + c * hJ ε x w := by
  unfold hJ
  simp only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_linearIndependent (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  have hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0 := by
    intro a
    refine (Cut.hJ_crd X v _ _).trans ?_
    have h := (VS D).herm.eq (X.eX a) (X.zu u)
    rw [(X.zu_orth u a).1] at h
    rw [← h]
    simp
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0 := by
    rw [HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]
    simp only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact ((D.mem u).A.T_prime).ne_zero
  have hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0 := by
    intro j a
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [Cut.hT_f_e X]
    split_ifs <;> simp
  have hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0 := by
    intro j
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [(X.zu_orth u j).2]
    simp
  rw [hfr, Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last _) = 0 := by
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg
    rw [hJ_lin] at h
    simp only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h
    unfold hJ at h
    simp only [mulVec_zero, dotProduct_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hzz
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_lin, hfz] at h
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h
  unfold hJ at h
  simp only [mulVec_zero, dotProduct_zero] at h
  exact h

end GlobalTheory.RationalFrame
