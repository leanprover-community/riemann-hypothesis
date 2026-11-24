module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def evInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace X.B.I.F => w.Completion) v)

def thetaInf (v : InfinitePlace X.B.I.F) : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E →+* ℂ :=
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evInf X v with commutes' := fun a => evV_algebraMap X.B.I v a } : Ainf X.B.I.F →ₐ[X.B.I.F] ℂ)
    ({ X.B.I.φ v with commutes' := X.B.I.φ_over v } : X.B.I.E →ₐ[X.B.I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thetaV_eq (v : InfinitePlace X.B.I.F) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    thetaV X.B.I v y = thetaInf X v (tensMap (E := X.B.I.E) (fstA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [thetaV_tmul]
    simp only [thetaInf, tensMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ofHAInf_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).1 = (splitA X.B.I.cm.sig X.B.I.J b).1) :
    ofHAInf X.B.I a = ofHAInf X.B.I b := by
  funext v
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, thetaV_eq]
  have := congrArg (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (thetaInf X v) this

theorem ofHAFin_congr (a b : HAd X.B.I)
    (h : (splitA X.B.I.cm.sig X.B.I.J a).2 = (splitA X.B.I.cm.sig X.B.I.J b).2) :
    ofHAFin X.B.I a = ofHAFin X.B.I b := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply, tauF_eq_comm]
  have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
  exact congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E) this

theorem eq_of_ofHA (p q : X.B.I.GA) (h1 : ofHAInf X.B.I (toHA X.B.I hb p) = ofHAInf X.B.I (toHA X.B.I hb q))
    (h2 : ofHAFin X.B.I (toHA X.B.I hb p) = ofHAFin X.B.I (toHA X.B.I hb q)) : p = q := by
  obtain ⟨a₁, b₁⟩ := (toHA_isBridge X.B.I hb) p
  obtain ⟨a₂, b₂⟩ := (toHA_isBridge X.B.I hb) q
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((a₁ v).trans ((congrFun h1 v).trans (a₂ v).symm)))
  · exact Subtype.ext (Units.ext (b₁.trans (h2.trans b₂.symm)))

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  unfold HidaSetting.toInf
  rw [show ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) by simp, map_mul, map_mul]
  rfl

theorem toHA_inf_one (hS : SplitIso) (x : X.B.I.Gf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, x))).1 = 1 := by
  apply PI.AprimeInfU.toHA_inf_one <;> assumption

theorem split_toHA (hS : SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  have e : p = (p.1, 1) * (1, p.2) := by simp
  conv_lhs => rw [e, map_mul, map_mul]
  refine Prod.ext ?_ ?_
  · show X.toInf hb p.1 * (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, p.2))).1 = _
    rw [toHA_inf_one X hb hS, mul_one]
  · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (p.1, 1))).2 * finHA X hb p.2 = _
    rw [toHA_fin_one X hb, one_mul]

theorem toInf_surjective (hS : SplitIso) : Function.Surjective (X.toInf hb) := by
  intro y
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  set p := (toHA X.B.I hb).symm (e.symm (y, 1))
  have hp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (y, 1) := by
    rw [← he]
    simp [p]
  have h2 : p.2 = 1 := eq_one_of_toHA_fin X hb p (by rw [hp])
  refine ⟨p.1, ?_⟩
  have := congrArg Prod.fst hp
  rw [split_toHA X hb hS] at this
  exact this

end Bridge

end MassDataMassesW
