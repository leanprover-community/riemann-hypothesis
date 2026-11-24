module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
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

theorem unimodInf_holds : UnimodInf := by
  intro D X u' ψ hT μinf νinf fibInf hP f h
  obtain ⟨hb, FdN, FdN', u, hX⟩ := hP.1
  have hG : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb) := hX.1.2.1
  obtain ⟨s, rfl⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds h
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : ContinuousMul (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    inferInstanceAs (ContinuousMul (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hmT : Measurable (X.toInf hb) := MassDataMassesW.measurable_toInf X hb
  have hms : Measurable fun x : X.B.I.Ginf => x * s := measurable_mul_const s
  have hpi : (Formalism.L2.SG.ProjRows.muInf X.B.I).map (fun x : X.B.I.Ginf => x * s) =
      Formalism.L2.SG.ProjRows.muInf X.B.I := by
    have hv : ∀ v, (Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v) = Formalism.REAL.muG (X.B.I.ε v) :=
      fun v => Formalism.REAL.indefinite_unitary_unimodular _ (X.B.I.ε v) (s v)
    haveI : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v)) := fun v => by
      rw [hv v]; infer_instance
    have e := Measure.pi_map_pi (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (f := fun v y => y * s v)
      (fun v => (measurable_mul_const (s v)).aemeasurable)
    simp only [hv] at e
    exact e
  have hm : X.measG.μGinf.map (fun g => g * X.toInf hb s) = X.measG.μGinf := by
    rw [hG, Measure.map_map (measurable_mul_const _) hmT]
    have e : (fun g => g * X.toInf hb s) ∘ X.toInf hb = X.toInf hb ∘ (fun x : X.B.I.Ginf => x * s) :=
      funext fun g => (PI.AprimeInfU.toInf_mul X hb g s).symm
    rw [e, ← Measure.map_map hmT hms, hpi]
  calc ∫⁻ g, f (g * X.toInf hb s) ∂X.measG.μGinf
      = ∫⁻ g, f g ∂(X.measG.μGinf.map (MeasurableEquiv.mulRight (X.toInf hb s))) :=
        (lintegral_map_equiv f (MeasurableEquiv.mulRight (X.toInf hb s))).symm
    _ = ∫⁻ g, f g ∂X.measG.μGinf := by
        rw [MeasurableEquiv.coe_mulRight, hm]

end PI.AprimeInfW
