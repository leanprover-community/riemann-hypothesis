module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
