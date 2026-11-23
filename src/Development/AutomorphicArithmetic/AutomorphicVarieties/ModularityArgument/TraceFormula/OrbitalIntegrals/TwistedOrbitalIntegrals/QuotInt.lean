module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotInt :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotInt := by
  intro hM G _ _ _ _ _ _ _ _ μG hμ H hH μ hh hi F hF hFH ⟨C, hC, hs⟩ ρ hρ
  obtain ⟨hf, hm⟩ := hM G μG hμ H hH μ hh hi ρ hρ
  obtain ⟨hcl, hfin⟩ := hm C hC
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have h1 : IntegrableOn (fun g => (ρ g).toReal) {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} μG :=
    integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 := ((integrable_indicator_iff hcl.measurableSet).2 h1).const_mul M
  refine h2.mono' (hF.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  · rw [Set.indicator_of_mem hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    obtain ⟨h, hh, c, hc, rfl⟩ := hg
    rw [hFH h hh]
    exact mul_le_mul_of_nonneg_right (hM c hc) ENNReal.toReal_nonneg
  · have : F g = 0 := by
      by_contra h0
      exact hg (hs g h0)
    simp [this, Set.indicator_of_notMem hg]
