module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensNu
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem euc_coords {V W : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure V) (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (c : ℝ)
    (h : μ.map e = ENNReal.ofReal c • volume) :
    ∃ eH : V ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ W)), (∀ x y, eH (x + y) = eH x + eH y) ∧
      μ.map eH = ENNReal.ofReal c • volume := by
  set R := (stdOrthonormalBasis ℝ W).repr with hR
  refine ⟨e.trans R.toHomeomorph, fun x y => ?_, ?_⟩
  · show R (e (x + y)) = R (e x) + R (e y)
    rw [he, map_add (f := _)]
  · have e1 : ((e.trans R.toHomeomorph : V ≃ₜ _) : V → _) = R ∘ e := rfl
    rw [e1, ← Measure.map_map R.continuous.measurable e.continuous.measurable, h, Measure.map_smul,
      R.measurePreserving.map_eq]
    exact R.continuous.measurable.aemeasurable

def HermEuc : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (η : Type) (_ : Fintype η) (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ),
      (∀ S T, eH (S + T) = eH S + eH T) ∧ νinf.map eH = ENNReal.ofReal cν • volume

theorem hermEuc : HermEuc := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) := ⟨rfl⟩
  obtain ⟨eH, hadd, hmap⟩ := euc_coords νinf (hermCoord X) (hermCoord_add X) _ (densNu_holds X u' ψ hT μinf νinf fibInf hP)
  exact ⟨_, inferInstance, eH, _, hadd, hmap⟩

end PI.AprimeInfW
