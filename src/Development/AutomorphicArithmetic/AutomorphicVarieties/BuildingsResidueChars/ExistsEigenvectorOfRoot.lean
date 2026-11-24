module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

open Polynomial

theorem UpperTheory.exists_eigenvector_of_root :
    ∀ {L C D W : Type} [Field L] [Field C] [AddCommGroup D] [Module L D] [FiniteDimensional L D] [AddCommGroup W] [Module C W] [FiniteDimensional C W] (s : L →+* C) (j : D →+ W) (S : Module.End L D) (T : Module.End C W), (∀ (a : L) (x : D), j (a • x) = s a • j x) → Submodule.span C (Set.range j) = ⊤ → (∀ x, T (j x) = j (S x)) → ∀ (q : L[X]) (b : C), b ∈ T.charpoly.roots → q.eval₂ s b = 0 → ∃ x : D, x ≠ 0 ∧ aeval S q x = 0 := by
  intro L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq
  by_contra hcon
  have hinj : Function.Injective (aeval S q) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    exact hcon ⟨x, h0, hx⟩
  have hsurj : Function.Surjective (aeval S q) := LinearMap.injective_iff_surjective.mp hinj
  have hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  have hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      intro x
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hr]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]
  have hsurj' : Function.Surjective (aeval T (q.map s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨j x, hcomm q x⟩
  have hinj' : Function.Injective (aeval T (q.map s)) :=
    LinearMap.injective_iff_surjective.mpr hsurj'
  have hroot : T.charpoly.IsRoot b := (mem_roots'.mp hb).2
  have hev : T.HasEigenvalue b := (Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv
  rw [eval_map, hq, zero_smul] at h1
  exact hv.2 (hinj' (by rw [h1, map_zero]))
