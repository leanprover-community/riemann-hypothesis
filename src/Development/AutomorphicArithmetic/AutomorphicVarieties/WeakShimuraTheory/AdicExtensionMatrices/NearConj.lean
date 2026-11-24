module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private theorem nc_wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

private theorem nc_apply {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) :
    tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem nc_diag {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i : Fin 4) : tconj t X i i = X i i := by
  rw [nc_apply, nc_wt_self]; simp [wv]

private theorem nc_smul {R : Type} [CommRing R] (t : Rˣ × Rˣ) (c : R) (X : M4 R) : tconj t (c • X) = c • tconj t X := by
  ext i j
  simp only [nc_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearConj :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} (t : Rˣ × Rˣ), Φ.Near a 0 D → ∃ D' : RD Φ R, Φ.Near a 0 D' ∧ (∀ g, D'.r g = tconj t (D.r g)) ∧ D'.ψ = D.ψ := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ D t h
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -, -⟩ := grp R
  let r' : Γ →* M4 R :=
    { toFun := fun g => tconj t (D.r g)
      map_one' := by rw [map_one, hone]
      map_mul' := fun g k => by rw [map_mul, hmul] }
  have hr : ∀ g, r' g = tconj t (D.r g) := fun _ => rfl
  refine ⟨⟨r', D.ψ⟩, ⟨⟨fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩, fun i j N => ?_, h.contψ, fun g i => ?_,
    fun g i j hij hτ => ?_, h.redψ⟩, hr, rfl⟩
  · have := h.rep.mult g
    unfold IsGSp at *
    show adj (tconj t (D.r g)) * tconj t (D.r g) = _
    rw [hadj, ← hmul, this, nc_smul, hone]
  · show tconj t (D.r g) = 1
    rw [h.rep.kill g hg, hone]
  · show tconj t (D.r Φ.g0) i j = 0
    rw [nc_apply, h.rep.nrm hij, mul_zero]
  · exact (h.cont i j N).comp fun x => Ideal.Quotient.mk _ (wv t (wt i j) : R) * x
  · show res Λ R (tconj t (D.r g) i i) = _
    rw [nc_diag, h.diag]
  · show tconj t (D.r g) i j ∈ _
    rw [nc_apply]
    exact Ideal.mul_mem_left _ _ (h.off g i j hij hτ)
