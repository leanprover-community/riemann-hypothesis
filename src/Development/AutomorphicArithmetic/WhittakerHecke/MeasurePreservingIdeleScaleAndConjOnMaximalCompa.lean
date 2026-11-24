module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
public import Development.AutomorphicArithmetic.WhittakerHecke.MaximalCompactMeasureMapConjDiagEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Compactness.Paracompact

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact :
    ∀ (M₀ : Meas ℚ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        MeasurePreserving (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) M₀.ν M₀.ν ∧
        MeasurableEmbedding (fun p : IdeleGroup ℚ × G1 ℚ => (Un.aa t u p.1, cD u p.2)) := by
  intro M₀ t u hu
  haveI := M₀.prob
  let c : IdeleGroup ℚ := (iy (Real.exp t) * u : (A ℚ)ˣ)
  have h1 : MeasurePreserving (fun z : IdeleGroup ℚ => c * z⁻¹) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    (measurePreserving_mul_left (ideleMeasure ℚ) c).comp (Measure.measurePreserving_inv (ideleMeasure ℚ))
  have h2 : MeasurePreserving (cD u : G1 ℚ → G1 ℚ) M₀.κ M₀.κ :=
    ⟨(M.continuous_cD u).measurable, UpperTheory.maximalCompact_measure_map_conjDiag_eq M₀ u hu⟩
  let e1 : IdeleGroup ℚ ≃ᵐ IdeleGroup ℚ := (MeasurableEquiv.inv (IdeleGroup ℚ)).trans (MeasurableEquiv.mulLeft c)
  let e2 : G1 ℚ ≃ᵐ G1 ℚ :=
    { toFun := cD u
      invFun := cD (u⁻¹ : (A ℚ)ˣ)
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      measurable_toFun := (M.continuous_cD u).measurable
      measurable_invFun := (M.continuous_cD _).measurable }
  exact ⟨h1.prod h2, (e1.prodCongr e2).measurableEmbedding⟩
