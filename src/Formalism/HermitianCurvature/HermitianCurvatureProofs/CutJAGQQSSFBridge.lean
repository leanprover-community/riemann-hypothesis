module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

theorem quadratic_transfer_identity : GQBridge := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg Y a b Φ
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hΦ : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φ.2
  have hF : Gauge.FamR P Bs (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    refine ⟨Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun c _ => Qx8.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_, ?_⟩
    · exact (Gauge.GC.GT.sec_pt P Bs hpl q).1.2.2
    · exact NFx1.TC.radSp_fam hΦ
    · intro c hc
      exact Qx8.slice_FF hz hz' hΦ hc
  have h := hg (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) hF Y a b
  funext ρ
  show MA.toSm P (Gauge.rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ')) ρ
  refine Eq.trans ?_ (h ρ)
  congr 1
  funext q
  unfold Gauge.rawR
  rw [X.t_apply (Y : ℂ) a b Φ _ (Gauge.GC.GT.sec_pt P Bs hpl q).1]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
