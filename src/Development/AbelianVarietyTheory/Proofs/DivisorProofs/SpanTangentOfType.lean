module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory

theorem span_tangent_of_type : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p d h : ℕ) (ty : Fin d → ZMod h)
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C), IsBasis G p ty γ →
    ∀ (t : ZMod h) (w : Fin d → C), (∀ c, ty c ≠ t → w c = 0) →
      w ∈ Submodule.span C (Set.range fun b : {b // ty b = t} => tangent (γ b.1)) := by
  intro C _ v p d h ty G γ hB t w hw
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (PTb.tmat γ).det = 0 := hdet
  have ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0 := by
    intro b c hc
    rw [PTb.tangent_eq_lc_zero G p (fun e => (hγ b e).1)]
    exact (hγty b).2 0 c (by simpa using hc)
  set x : Fin d → C := Matrix.vecMul w (PTb.tmat γ)⁻¹ with hx
  have hxw : Matrix.vecMul x (PTb.tmat γ) = w := PTb.vecMul_inv_tmat hdet' w
  have hsupp : ∀ b, ty b ≠ t → x b = 0 :=
    PTb.vecMul_tmat_support ty hdet' ht x t (fun c hc => by rw [hxw]; exact hw c hc)
  have hsum : w = ∑ b, x b • tangent (γ b) := by rw [PTb.sum_smul_tangent, hxw]
  rw [hsum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : ty b = t
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)
  · rw [hsupp b hb, zero_smul]; exact Submodule.zero_mem _

end GlobalTheory
