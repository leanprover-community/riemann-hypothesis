module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPolD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnitsOpenTens : Prop := ∀ {D : D7} (X : HidaSetting D), IsOpen {z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E | IsUnit z}

theorem isUnit_det_TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) :
    IsUnit (TI X u' hT).1.det := by
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem nearFacts_of (hU : UnitsOpenTens) : NearFacts := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hCh
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨hmr, hcomp, hsmul, hgram, hcTmul, hcT1, -, -⟩ := rmulFacts_holds X
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hdetc : ContinuousAt (fun T => (a T).det) (TI X u' hT) :=
    (continuous_id.matrix_det).continuousAt.comp hCh.2.2.1
  have hU1 : {T | IsUnit (a T).det} ∈ 𝓝 (TI X u' hT) :=
    hdetc.preimage_mem_nhds ((hU X).mem_nhds (by
      show IsUnit (a (TI X u' hT)).det
      rw [hCh.2.1, Matrix.det_one]; exact isUnit_one))
  refine ⟨Ω ∩ {T | IsUnit (a T).det}, Set.inter_subset_left, Filter.inter_mem hCh.1 hU1, fun T hT1 =>
    ⟨(Matrix.isUnit_iff_isUnit_det _).2 hT1.2, fun Y hY => ?_⟩⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [hY, ← hCh.2.2.2 T hT1.1, hgram, gramR_Y0_eq_TI X u' hT, Matrix.det_mul, Matrix.det_mul]
  have hc : (cTI X (a T)).det = sigR (Ainf X.B.I.F) X.B.I.cm.sig (a T).det := by
    rw [cTI, Matrix.det_transpose, RingHom.map_det]
    rfl
  rw [hc]
  exact ((hT1.2.map _).mul (isUnit_det_TI X u' hT hd)).mul hT1.2

end PI.AprimeInfW
