module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.ContDiffMulRight
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by
  have hw' : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x w) := hw
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (σ g w))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hFeq⟩ := hw' (g₀ * g) (mul_mem_UH (a := g₀) hg₀ hg)
  refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g),
    hU.preimage (contDiff_mulRight g).continuous, hmem, ?_, ?_⟩
  · exact hF.comp (contDiff_mulRight g).contDiffOn (fun x hx => hx)
  · intro x hx hxI
    have e : σ (x * g) w = F (x * g) := hFeq (x * g) hx (mul_mem_UH hxI hg)
    show σ x (σ g w) = F (x * g)
    rw [← e, hmul.2 x hxI g hg, ContinuousLinearMap.comp_apply]

end PI.PhMeasCore.UnitaryGroupMassFormula

end
