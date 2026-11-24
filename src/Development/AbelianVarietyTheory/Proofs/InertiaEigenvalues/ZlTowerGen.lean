module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.WeakClosed

set_option synthInstance.maxHeartbeats 400000

instance vrOCb (l : ℕ) [Fact l.Prime] : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

@[reducible] def cbValued (l : ℕ) [Fact l.Prime] :
    Valued (Cb l) (ValuationRing.ValueGroup (OCb l) (Cb l)) :=
  Valued.mk' (ValuationRing.valuation (OCb l) (Cb l))

@[reducible] def cbTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (Cb l) :=
  (cbValued l).toUniformSpace.toTopologicalSpace

@[reducible] def wTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (WCb l) :=
  @GlobalTheory.WeakTop.wittTop l (Cb l) (cbTop l)

variable {l : ℕ} [Fact l.Prime]

@[reducible] def zlMod {K LL : FinExt l} (T : Lt K LL) : Module ℤ_[l] ↥T.L.T :=
  Module.compHom ↥T.L.T (algebraMap ℤ_[l] ↥(OL LL))

theorem zlTower_gen {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup M] [Module O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    IsScalarTower ℤ_[l] O M :=
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

theorem zlTower {K LL : FinExt l} (T : Lt K LL) :
    @IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T _ _ (zlMod T).toSMul :=
  zlTower_gen

abbrev LatB {K LL : FinExt l} (T : Lt K LL) (d : ℕ) : Type :=
  @Module.Basis (Fin d) ℤ_[l] ↥T.L.T _ _ (zlMod T)

@[reducible] def twTop {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) :
    TopologicalSpace (TW (RW LL) T) :=
  letI := zlMod T
  haveI := zlTower T
  TopologicalSpace.induced (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
    (@Pi.topologicalSpace (Fin d) (fun _ => WCb l) (fun _ => wTop l))

@[reducible] def oTop {LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace ↥(OL LL) :=
  TopologicalSpace.induced bO.equivFun inferInstance

@[reducible] def aTop {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace (AA K LL) :=
  letI := oTop bO
  @Pi.topologicalSpace _ _ fun _ => PowerSeries.WithPiTopology.instTopologicalSpace ↥(OL LL)

end GlobalTheory.WeakClosed
