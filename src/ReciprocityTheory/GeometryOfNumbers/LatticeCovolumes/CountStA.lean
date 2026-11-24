module

public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurePreservingSwapPi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module NumberField Set

set_option backward.isDefEq.respectTransparency.types false in
theorem covol_div_covol_eq_relIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ / ZLattice.covolume L₂ μ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  let e : Module.Free.ChooseBasisIndex ℤ L₁ ≃ Module.Free.ChooseBasisIndex ℤ L₂ :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
        ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂])
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex e
  let b₀ := b₂.ofZLatticeBasis ℝ L₂
  have h1 := ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ b₀
  have h2 := ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ b₀
  have hb : ((↑) ∘ b₂ : _ → E) = ⇑b₀ := by ext i; simp [b₀, Basis.ofZLatticeBasis_apply]
  rw [hb, Basis.det_self, abs_one, one_mul] at h2
  have hpos := ZLattice.covolume_pos L₂ μ
  rw [h2] at hpos
  rw [h1, h2, mul_div_assoc, div_self hpos.ne', mul_one,
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (Submodule.coe_mem _)⟩ i)

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder
open Matrix

section Form

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem HermFam.form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm, h.smul_right, map_mul, h.conj_symm]

theorem HermFam.form_sum_right (h : HermFam K V) (σ : K →+* ℂ) (x : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, h.form σ x (f i) :=
  map_sum (AddMonoidHom.mk' (h.form σ x) (h.add_right σ x)) f s

theorem HermFam.form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by

  rw [← h.conj_symm, h.form_sum_right, map_sum]
  simp only [h.conj_symm]

theorem HermFam.form_expand (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (c : Fin n → K)
    (v : Fin n → V) :
    h.form σ (∑ i, c i • v i) (∑ j, c j • v j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * h.gram σ v i j * σ (c j) := by
  rw [h.form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.form_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.form_smul_left, h.smul_right, HermFam.gram, Matrix.of_apply]
  ring

end Form

end ReciprocityTheory.GeometryOfNumbersTheory
