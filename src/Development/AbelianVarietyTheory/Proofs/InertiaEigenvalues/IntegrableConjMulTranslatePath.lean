module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
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

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory

theorem integrable_conj_mul_translate_path {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (c : ℝ → G) (hc : Continuous c) {f' : G → ℂ} (hf' : MemL2Quotient Γ μ f')
    (_hcont : Continuous f') (H : L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
  have hm : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => rmul Γ (c s) q) :=
    measurable_rmul_uncurry.comp (measurable_snd.prodMk (hc.measurable.comp measurable_fst))
  have hp := (MeasurePreserving.id (volume.restrict (Set.uIoc (0 : ℝ) t))).skew_product
    (μc := quotMeasure Γ μ) (μd := quotMeasure Γ μ) hm
    (Filter.Eventually.of_forall fun s => (measurePreserving_rmul (c s)).map_eq)
  have h1 := ((Lp.memLp H).star).comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))
  have h2 := (hf'.2.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))).comp_measurePreserving hp
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  have e : descend Γ f' (rmul Γ (c p.1) p.2) = f' (sec Γ p.2 * c p.1) := by
    rw [← hf'.1.descend_mk, ← rmul_mk, mk_sec]
  change star (H p.2) * descend Γ f' (rmul Γ (c p.1) p.2) = _
  rw [e]
  rfl

end GlobalTheory
