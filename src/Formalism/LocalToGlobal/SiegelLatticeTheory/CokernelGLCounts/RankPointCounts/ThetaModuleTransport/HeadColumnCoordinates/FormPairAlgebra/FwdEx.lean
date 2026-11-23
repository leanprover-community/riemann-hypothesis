module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ElimSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.FormCLR
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

theorem fwdEx : FwdEx := by
  intro E _ O cj hcj hO r t t' ht ht' Z₁ Z₂ hu₁ hu₂ hk hg₁ hg₂ θ hθ
  have hη₁ : EtaNZD O cj Z₁ (t : E) (t' : E) := eta_nzd O cj hcj Z₁ hu₁ _ _ hg₁
  have hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E) := eta_nzd O cj hcj Z₂ hu₂ _ _ hg₂
  have hΓ := hθ.2.1
  have hΓ' := hθ.2.2
  have sL := fun m => gEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ' m
  have sR := fun m => gsEquiv_spec O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ m
  refine ⟨⟨(gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ',
      gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ),
      ⟨g_b O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hk hΓ hΓ',
        g_e O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hk hΓ hΓ'⟩, ?_, ?_⟩,
    fun m => (sL m).1, fun m => (sR m).1⟩
  · intro y' y₂' h
    have key := (sR (Submodule.Quotient.mk y')).2
    rw [h, lamSQ_mk, lamSQ_mk] at key
    exact key
  · intro y y' y₂ y₂' h h'
    exact fwd_B O cj hcj hO t t' ht ht' hu₁ hu₂ hk hg₁ hg₂ θ hθ
      (gEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ').toLinearMap
      (gsEquiv O cj hO t t' Z₁ Z₂ θ hu₁ hu₂ hη₁ hη₂ hΓ).toLinearMap
      (fun m => (sL m).1) (fun m => (sR m).1) (fun m => (sL m).2) (fun m => (sR m).2)
      y y' y₂ y₂' h h'

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
