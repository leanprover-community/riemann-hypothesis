module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
