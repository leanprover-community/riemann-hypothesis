module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {F : Type} [Field F] [NumberField F]

theorem exists_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {κ' κ'' : Type} [Fintype κ'] [Fintype κ'']
    (f : SchwartzMap (κ' ⊕ κ'' → W) ℂ) :
    ∃ f' : SchwartzMap (κ' → W) ℂ, ∀ v, f' v = f (Sum.elim v 0) := by
  let ι : (κ' → W) →L[ℝ] (κ' ⊕ κ'' → W) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun i => ContinuousLinearMap.proj i) (fun _ => 0) j
  have hι : ∀ v, ι v = Sum.elim v 0 := fun v => by funext j; rcases j with j | j <;> rfl
  have hn : ∀ v, ‖v‖ ≤ ‖ι v‖ := fun v => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (ι v) (Sum.inl i)
    rw [hι] at this ⊢
    simpa using this
  refine ⟨SchwartzMap.compCLM ℂ (g := ι) ι.hasTemperateGrowth ⟨1, 1, fun v => ?_⟩ f, fun v => ?_⟩
  · rw [one_mul, pow_one]; linarith [hn v]
  · simp [hι]

theorem sb_slice {X : Type} [TopologicalSpace X] [Zero X] [T2Space X] {κ' κ'' : Type}
    {g : (κ' ⊕ κ'' → X) → ℂ} (hg : g ∈ SB (κ' ⊕ κ'' → X)) : (fun z : κ' → X => g (Sum.elim z 0)) ∈ SB (κ' → X) := by
  have hc : Continuous fun z : κ' → X => (Sum.elim z 0 : κ' ⊕ κ'' → X) := by
    refine continuous_pi fun j => ?_
    rcases j with j | j
    · exact continuous_apply j
    · exact continuous_const
  refine ⟨hg.1.comp_continuous hc, ?_⟩
  have hK : IsCompact ((fun x : κ' ⊕ κ'' → X => x ∘ Sum.inl) '' tsupport g) :=
    hg.2.isCompact.image (continuous_pi fun i => continuous_apply _)
  refine HasCompactSupport.intro' hK hK.isClosed fun z hz => ?_
  by_contra hne
  apply hz
  exact ⟨Sum.elim z 0, subset_tsupport _ hne, rfl⟩

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
