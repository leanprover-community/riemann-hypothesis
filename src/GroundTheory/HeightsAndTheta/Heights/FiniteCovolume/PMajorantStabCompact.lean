module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
