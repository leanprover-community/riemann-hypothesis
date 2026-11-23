module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaBridgeHalves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
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

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaDictAllC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')), s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
      (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D))

theorem levi_split_iff {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam') :
    (iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂ ↔
      AdTriv X ((((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u)⁻¹ * (s₂.pt * s₁.pt⁻¹).2 *
        (((Y.cs u).h ((Y.cs u).base s₁.lam) : X.B.I.Gf) * X.xu u))) := by
  obtain ⟨gδ, -, hs⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  rw [hb2, AdTriv, ← IotaDictPf.levi_one_iff Y.TR gδ, hs]
  constructor
  · intro h
    exact mul_right_cancel (h.symm.trans (one_mul _).symm)
  · intro h
    rw [h, one_mul]

theorem iotaDict_fwd {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Formalism.L2.SG.Full.Full X) {u u' : D.what₂.Word}
    (s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hl : s₁.lam = s₂.lam) (hl' : s₁.lam' = s₂.lam')
    (h : iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂) :
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) := by
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl']
  refine iotaBridgeARC_holds _ X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) ?_
  exact (levi_split_iff Y s₁ s₂ hl hl').1 h

theorem iotaDictAllC_of (h2 : IotaBridgeRAC) : IotaDictAllC := by
  intro D X Y u u' s₁ s₂ hl hl'
  refine ⟨iotaDict_fwd Y s₁ s₂ hl hl', fun h => ?_⟩
  obtain ⟨gδ, nδ, -⟩ := IotaDictPf.iotaOf_split Y s₁ s₂ hl hl'
  have hb2 : (s₂.pt * s₁.pt⁻¹).2 = s₂.pt.2 * s₁.pt.2⁻¹ := by rw [Prod.snd_mul, Prod.snd_inv]
  have hRL : RatLink X (s₂.pt * s₁.pt⁻¹) (s₂.lin * s₁.lin⁻¹) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X s₂.rep.2.1 (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X s₁.rep.2.1)
  rw [Formalism.L2.SG.Pf.Act.ratIotaC' Y u u' s₁ s₂ hl hl'] at h
  exact (levi_split_iff Y s₁ s₂ hl hl').2
    (h2 D X Y u s₁.lam s₁.mem _ _ hRL (by rw [hb2]; exact gδ.1.1) (by rw [hb2]; exact nδ) h)

theorem iotaDictC_holds_of (h2 : IotaBridgeRAC) : IotaDictC :=
  fun D X Y u u' s₁ s₂ _ _ _ _ hl hl' => iotaDictAllC_of h2 D X Y u u' s₁ s₂ hl hl'

end Formalism.L2.SG.Pf
