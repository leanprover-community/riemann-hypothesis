module

public import Formalism.JumpKernelCokernel.Statement
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

@[expose] public section

namespace Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module

theorem ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → O)
    (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

end Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module in
theorem Formalism.KernelCokernelLengths.determinant_length_formula : Formalism.KernelCokernelLengths.DetLen := by
  intro O _ _ _ M _ _ _ _ d hdet
  classical
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  let e : M ≃ₗ[O] LinearMap.range d := LinearEquiv.ofInjective d hinj
  have h : finrank O (LinearMap.range d) = finrank O M := e.finrank_eq.symm
  let b := Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h

  have hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i) := by
    rw [((LinearMap.range d).quotientEquivPiSpan b h).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let u : M ≃ₗ[O] LinearMap.range d := b'.equiv ab (Equiv.refl _)
  let D : M →ₗ[O] M := (LinearMap.range d).subtype ∘ₗ u.toLinearMap
  have hD : LinearMap.det D = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul,
        Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
        Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [this, Matrix.det_diagonal]
  have hd : d = D ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp [D, e]
  have hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap := by
    rw [congrArg LinearMap.det hd, LinearMap.det_comp, hD]
  rw [hL]
  change _ = Ring.ord O (LinearMap.det d)
  rw [hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _),
    Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]
