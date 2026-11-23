module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.RmulFactsHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.WittInfHolds
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem wittNear_holds : WittNear := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a Ω' a₂ hC hC₂ T hTm hU
  obtain ⟨-, hmul, hsm, hgr, hcT, hc1, -, -⟩ := rmulFacts_holds X
  obtain ⟨u, hu⟩ := hU
  set w : TupI X := rmulT X (↑u⁻¹ : MfI X) (rmulT X (a T) (Y0 X u')) with hw
  have hgT : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC.2.2.2 T hTm.1
  have hgT₂ : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (rmulT X (a₂ T) (Y0 X u')) = (T : Matrix _ _ _) :=
    hC₂.2.2.2 T hTm.2
  have hY0 : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (Y0 X u') =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) :=
    gramR_ratTup (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
  have hinv1 : cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X) = 1 := by
    rw [← hcT, Units.mul_inv, hc1]
  have hgw : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J w =
      (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) := by
    rw [hw, hgr, hgT, ← hgT₂, ← hu, hgr, hY0]
    rw [show cTI X (↑u⁻¹ : MfI X) * (cTI X (↑u : MfI X) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) * (↑u : MfI X)) *
        (↑u⁻¹ : MfI X) = (cTI X (↑u⁻¹ : MfI X) * cTI X (↑u : MfI X)) *
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F)) *
        ((↑u : MfI X) * (↑u⁻¹ : MfI X)) by simp only [Matrix.mul_assoc],
      hinv1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hfix : ∀ b : X.B.I.E, X.B.I.cm.sig b = b ↔ b ∈ (algebraMap X.B.I.F X.B.I.E).range :=
    fun b => X.B.I.cm.fixed b
  have hinv : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hJ : IsHermND X.B.I.cm.sig X.B.I.J := by
    refine ⟨fun i j => ?_, X.B.I.J_det⟩
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  have hUC : PIW.AdelicOrbitU.UnitChoice (Ainf X.B.I.F) :=
    PIW.AdelicOrbitU.uc_pi (fun v : NumberField.InfinitePlace X.B.I.F => v.Completion)
  obtain ⟨g, hg⟩ := PI.AprimeInfWitt.witt_R X.B.I.cm.sig h2 hfix hinv X.B.I.J hJ (tupH (frameOf X u')) hT hdet
    (Ainf X.B.I.F) hUC w hgw
  refine ⟨g, ?_⟩
  have hback : rmulT X (↑u : MfI X) w = rmulT X (a T) (Y0 X u') := by
    rw [hw, hmul, Units.inv_mul, rmulT_one]
  rw [← hback, ← hu, hsm]
  congr 1
  exact hg.symm

end PI.AprimeInfW
