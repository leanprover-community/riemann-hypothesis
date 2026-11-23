module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegrableRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep

theorem rep_parametric_integral : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin T _ _ _ _ _ ν _ Q w φ hQ hw hφ hrep
  have hcont : Continuous fun x => ∫ t in Q, φ t x ∂ν :=
    continuous_parametric_integral_of_continuous (f := fun x t => φ t x)
      (hφ.comp continuous_swap) hQ
  refine ⟨hcont, rep_of_pairing hloc hcont.locallyIntegrable fun C hC => ?_⟩
  obtain ⟨Λ, hΛ⟩ := exists_pairing hloc hlin hC
  have hwi : IntegrableOn w Q ν := hw.continuousOn.integrableOn_compact hQ
  have hint : Integrable (Function.uncurry φ) ((ν.restrict Q).prod (μ.restrict C)) := by
    rw [Measure.prod_restrict]
    exact hφ.continuousOn.integrableOn_compact (hQ.prod hC)
  rw [← hΛ, ← Λ.integral_comp_comm hwi, ← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hΛ]
  exact integral_congr_ae (ae_restrict_of_ae (hrep t))

end GlobalTheory.LocRep
