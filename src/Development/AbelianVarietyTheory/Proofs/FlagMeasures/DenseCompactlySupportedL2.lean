module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CompactDense

theorem dense_of_sigmaCompact {X : Type} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) :
    Dense {y : Lp ℂ 2 μ | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0} := by
  intro y
  have hm : ∀ n, MeasurableSet (compactCovering X n) := fun n => (isCompact_compactCovering X n).isClosed.measurableSet
  have hy : MemLp (y : X → ℂ) 2 μ := Lp.memLp y
  let u : ℕ → Lp ℂ 2 μ := fun n => (hy.indicator (hm n).nullMeasurableSet).toLp _
  have hu : ∀ n, (u n : X → ℂ) =ᵐ[μ] (compactCovering X n).indicator y := fun n => MemLp.coeFn_toLp _
  refine mem_closure_of_tendsto (f := u) (b := Filter.atTop) ?_ (Filter.Eventually.of_forall fun n => ?_)
  · have hi : Integrable (fun z => ‖(y : X → ℂ) z‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).1 hy
    have e : ∀ n, ‖u n - y‖ ^ 2 = ∫ z, (compactCovering X n)ᶜ.indicator (fun z => ‖(y : X → ℂ) z‖ ^ 2) z ∂μ := by
      intro n
      rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
      refine integral_congr_ae ?_
      filter_upwards [hu n, Lp.coeFn_sub (u n) y] with z h1 h2
      rw [inner_self_eq_norm_sq, h2, Pi.sub_apply, h1]
      by_cases hz : z ∈ compactCovering X n <;> simp [hz]
    have h0 : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2) Filter.atTop (nhds (∫ _z, (0 : ℝ) ∂μ)) := by
      simp only [e]
      refine tendsto_integral_of_dominated_convergence _ (fun n => hi.1.indicator (hm n).compl) hi
        (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
      · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
        simp
      · obtain ⟨N, hN⟩ := exists_mem_compactCovering z
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have : z ∈ compactCovering X n := compactCovering_subset X hn hN
        simp [this]
    rw [integral_zero] at h0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 := h0.sqrt
    simpa using h1
  · refine ⟨_, isCompact_compactCovering X n, ?_⟩
    filter_upwards [hu n] with z h hz
    simp [h, hz]

theorem dense_compact_support : ∀ B : RowsAut, Dense {y : B.I.L2 B.μf B.fund | ∃ C : Set B.I.GA, IsCompact C ∧ ∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0} := by
  intro B
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  exact dense_of_sigmaCompact _

end GlobalTheory.CompactDense
