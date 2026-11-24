module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

private theorem semi_symm {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) : IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [h]
  simp

private theorem exists_basis {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ b' : Module.Basis ι ℂ V', ∀ y i, b'.repr y i = σ (b.repr (e.symm y) i) := by
  refine ⟨Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))
      invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        have hs := semi_symm h c y
        simp [hs]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }, ?_⟩
  intro y i
  rfl

theorem UpperTheory.Gal.LocalSmoothExtension.traceSemi_of :
    TraceSemi := by
  intro σ V V' _ _ _ _ e h T T' hT
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    obtain ⟨b', hb'⟩ := exists_basis h b
    have hbj : ∀ j, b' j = e (b j) := by
      intro j
      apply b'.repr.injective
      rw [b'.repr_self]
      ext k
      rw [hb', AddEquiv.symm_apply_apply, b.repr_self]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [Finsupp.single_apply, hjk]

    rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace,
    Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT,
      AddEquiv.symm_apply_apply]
  · have H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V') := by
      rintro ⟨t, ⟨c⟩⟩
      obtain ⟨c', -⟩ := exists_basis (semi_symm h) c
      exact H ⟨_, ⟨c'.reindexFinsetRange⟩⟩
    simp only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]
