module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GaussianSphereMeanIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  intro n e h G hint
  have hfin := (gaussM_univ_pos_lt_top (e + 1) n).2
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hfin⟩
  haveI : IsFiniteMeasure (volume.restrict (ballProd h e)) := ⟨by rw [Measure.restrict_apply_univ]; exact volume_ballProd_lt_top h e⟩
  obtain ⟨a, ha⟩ := ModelDimension.GSph.map_coefRows (e := e) h
  have hmap : Measure.map (coefRows h) (gaussM (e + 1) n) = Measure.map ModelDimension.GSph.scT ((a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)).prod (volume.restrict (ballProd h e))) := by
    rw [ha, ModelDimension.GSph.layer, Measure.prod_smul_left, Measure.map_smul]
    exact ModelDimension.GSph.measurable_scT.aemeasurable
  have h1 : ∀ᵐ x ∂ModelDimension.GSph.ex1, 0 < x :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp : ∀ᵐ s ∂(ModelDimension.GSph.exP e), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin e => ModelDimension.GSph.ex1) (i := i)).eventually h1
  have hpos0 : ∀ᵐ s ∂((ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    (withDensity_absolutelyContinuous _ _).ae_le hp
  have hpos : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    Measure.ae_smul_measure hpos0 a
  have hne : (volume.restrict (ballProd h e)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (volume_ballProd_pos h e).ne'
  have haesm : AEStronglyMeasurable (fun u => G (nrmGroups h e u)) (Measure.map (coefRows h) (gaussM (e + 1) n)) := by
    rw [ha]
    exact ((ModelDimension.GSph.aesm h G hint.1).mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure a
  have hinv : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ u, (fun u => G (nrmGroups h e u)) (ModelDimension.GSph.scT (s, u)) = (fun u => G (nrmGroups h e u)) u := by
    filter_upwards [hpos] with s hs u
    exact congrArg G (ModelDimension.GSph.nrm_sc h (fun i => Real.sqrt_pos.mpr (hs i)) u)
  have key := ModelDimension.GSph.transfer (gaussM (e + 1) n) (a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)) (volume.restrict (ballProd h e)) hne (ModelDimension.GSph.measurable_coefRows h) ModelDimension.GSph.measurable_scT hmap haesm hinv hint
  refine ⟨key.1, ?_⟩
  rw [key.2]
  rfl
