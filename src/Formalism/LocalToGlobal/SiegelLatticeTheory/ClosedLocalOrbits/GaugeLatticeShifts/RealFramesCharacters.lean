module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormRegularity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
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

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealFramesCharacters

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fam_rv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  induction a using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u]; rfl
  | cast b => simp only [fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u]; rfl

theorem rv_sum (v : InfinitePlace X.B.I.F) {ι : Type} (t : Finset ι) (c : ι → X.B.I.E) (y : ι → Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (∑ i ∈ t, c i • y i) = ∑ i ∈ t, X.B.I.φ v (c i) • rv X.B.I v (y i) := by
  unfold rv
  have h : (fun j => X.B.I.φ v ((∑ i ∈ t, c i • y i) j)) =
      ∑ i ∈ t, X.B.I.φ v (c i) • (fun j => X.B.I.φ v (y i j)) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_sum]
  congr 1
  funext i
  rw [Matrix.mulVec_smul]

theorem real_frame (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) (v : InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    uMat (x.1 v) *ᵥ fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a =
      ∑ c, X.B.I.φ v (X.ιE.symm (un c a)) • fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) c := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  simp only [fam_rv]
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd, hun, Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  rw [rv_sum]

theorem psiInf_rat (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp un) := by
  refine FormRegularity.psi_of_frame X u x.1 (fun v => (un.map (fun t => X.B.I.φ v (X.ιE.symm t)))ᵀ)
    (fun v a => by simpa [Matrix.transpose_apply, Matrix.map_apply] using real_frame X u hRL un hun v a) _ fun v => ?_

  simp only [Matrix.transpose_apply, Matrix.map_apply, FormRegularity.sgUp_eq, map_sum, star_sum, ← Finset.sum_add_distrib]

end Formalism.L2.SG.RealObj.RealFramesCharacters
