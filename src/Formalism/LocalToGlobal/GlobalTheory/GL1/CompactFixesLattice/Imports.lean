module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E) (D : 𝓞 F), D ≠ 0 ∧ (∀ i, b i ∈ intOE E) ∧
      ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun j =>
    algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)
  have hspanQ : Submodule.span ℚ (Set.range β) = ⊤ := by
    have h := (NumberField.integralBasis E).span_eq
    have hr : Set.range (NumberField.integralBasis E) = Set.range β := by
      ext x
      simp [β, NumberField.integralBasis_apply]
    rw [hr] at h
    exact h
  have hspan : Submodule.span F (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range β) := by rw [hspanQ]; exact Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ F _ hx
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F (Set.range β)
  have hBfin : B.Finite := (Set.finite_range β).subset hBsub
  haveI := hBfin.fintype
  let e := Fintype.equivFin B
  let b0 : Module.Basis B F E := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])
  let b : Module.Basis (Fin (Fintype.card B)) F E := b0.reindex e
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image
      fun p => b.repr (β p.1) p.2)
  refine ⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩
  · intro i
    have hbi : b i = ((e.symm i : B) : E) := by simp [b, b0]
    obtain ⟨j, hj⟩ := hBsub (e.symm i).2
    rw [hbi, ← hj]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx i
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    have key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range := by
      intro j
      obtain ⟨z, hz⟩ := hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)
      refine RingHom.mem_range.mpr ⟨z, ?_⟩
      rw [hz, Algebra.smul_def]
    have hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j := by
      conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]

      rw [map_sum]
      simp [β, map_zsmul]
    rw [hxe]

    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    exact Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
