module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GxDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ZxMul

theorem zx_mul : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  intro D X u u' g γ h v C B hC hB
  have hU : (uMat (g⁻¹ v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (g⁻¹ v) = Formalism.REAL.Jm (X.B.I.ε v) := (g⁻¹ v).2
  have e : uMat ((g * γ * h) v) = uMat (g v) * uMat (γ v) * uMat (h v) := rfl
  have hL : ∀ a, uMat (g⁻¹ v) *ᵥ Formalism.L2.SG.RealObj.frm X u 1 v a =
      ∑ c, Cᵀ a c • Formalism.L2.SG.RealObj.frm X u 1 v c := fun a => by
    rw [hC a]; rfl
  have hM : ∀ b, uMat (h v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b =
      ∑ d, Bᵀ b d • Formalism.L2.SG.RealObj.frm X u' 1 v d := fun b => by
    rw [hB b]; rfl
  unfold Formalism.L2.SG.RealObj.ZX
  rw [e, GlobalTheory.GxConj.zhat_conj _ _ _ _ _ _ _
    (GlobalTheory.GxConj.hJ_adj _ _ _ hU (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v))) _ _ hL hM,
    Matrix.transpose_transpose]
  rfl

end GlobalTheory.ZxMul
