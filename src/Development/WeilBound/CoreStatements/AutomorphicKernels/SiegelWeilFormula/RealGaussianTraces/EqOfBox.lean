module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

open Topology in
theorem eq_of_box {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (hB : IsOpen B) (g1 g2 : X → ℂ)
    (h1 : ContinuousOn g1 B) (h2 : ContinuousOn g2 B) (t : X) (ht : t ∈ B)
    (hbox : ∀ U ∈ 𝓝 t, ∃ S, IsCompact S ∧ S ⊆ U ∧ S ⊆ B ∧ S ∈ 𝓝 t ∧ ∫ x in S, g1 x ∂ν = ∫ x in S, g2 x ∂ν) :
    g1 t = g2 t := by
  by_contra hne
  set c := g1 t - g2 t with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hne
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hcont : ContinuousAt (fun x => g1 x - g2 x) t := (h1.sub h2).continuousAt (hB.mem_nhds ht)
  have hU : {x | ‖(g1 x - g2 x) - c‖ < ‖c‖ / 2} ∈ 𝓝 t := by
    have := hcont.eventually (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ‖c‖ / 2))
    filter_upwards [this] with x hx
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  obtain ⟨S, hSc, hSU, hSB, hSt, hint⟩ := hbox _ hU
  have hSfin : ν S < ⊤ := hSc.measure_lt_top
  have hSpos : 0 < ν S := Measure.measure_pos_of_mem_nhds (μ := ν) hSt
  have hSr : 0 < ν.real S := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hi1 : IntegrableOn g1 S ν := (h1.mono hSB).integrableOn_compact hSc
  have hi2 : IntegrableOn g2 S ν := (h2.mono hSB).integrableOn_compact hSc
  have hi12 : IntegrableOn (fun x => g1 x - g2 x) S ν := hi1.sub hi2
  have hic : IntegrableOn (fun _ : X => c) S ν := integrableOn_const hSfin.ne
  have h0 : ∫ x in S, (g1 x - g2 x - c) ∂ν = -(ν.real S • c) := by
    rw [integral_sub hi12 hic, integral_sub hi1 hi2, hint, sub_self, setIntegral_const, zero_sub]
  have hle : ‖∫ x in S, (g1 x - g2 x - c) ∂ν‖ ≤ ‖c‖ / 2 * ν.real S :=
    norm_setIntegral_le_of_norm_le_const hSfin (fun x hx => (hSU hx).le)
  rw [h0, norm_neg, norm_smul, Real.norm_of_nonneg hSr.le] at hle
  nlinarith

end PositivityTheory.SiegelWeilFormula.GReal
