module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem conjW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  intro F E _ _ _ _ _ σ B hB v w hw
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hc : GlobalTheory.LFun.IsConjAt σ h (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
    congrArg (fun z => GlobalTheory.LFun.toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
      ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm_apply_apply y)
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨hcc, -⟩ := hU
  refine ⟨hcc, fun x hx => GlobalTheory.LFun.InertChart.conj_mem hw hc hx, ?_,
    fun e => GlobalTheory.LFun.InertChart.conj_algebraMap hc e⟩
  have h2 := GlobalTheory.LFun.complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
  rw [GlobalTheory.LFun.complMap_algebraMap] at h2
  rwa [map_inv₀, map_inv₀, map_ofNat, map_ofNat] at h2

end GlobalTheory.InertBigCell
