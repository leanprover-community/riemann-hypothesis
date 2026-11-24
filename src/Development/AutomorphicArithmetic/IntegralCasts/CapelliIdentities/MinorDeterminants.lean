module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card := by
  intro N J
  rfl

noncomputable def UpperTheory.Reformulated.B.MinorDeterminants.minorIJ :
    {R : Type} → [CommRing R] → {N : ℕ} → Matrix (Fin N) (Fin N) R → Finset (Fin N) → Finset (Fin N) → R :=
    fun {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) ↦
      if e : I.card = J.card then
        (h.submatrix (⇑(I.orderEmbOfFin e) : Fin J.card → Fin N)
            (⇑(J.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 J)) : Fin J.card → Fin N)).det
      else (0 : R)

theorem UpperTheory.Reformulated.B.MinorDeterminants.main :
    ∀ {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (f : Fin S.card → Fin N),
      Function.Injective f →
        UpperTheory.Reformulated.B.MinorDeterminants.minorIJ C (Finset.image f Finset.univ) S = (0 : ℂ) →
          (C.submatrix f (⇑(S.orderEmbOfFin rfl) : Fin S.card → Fin N)).det = (0 : ℂ) := by
  intro N C S f hf h0
  have e : (Finset.image f Finset.univ).card = S.card := by
    rw [Finset.card_image_of_injective _ hf]; simp
  unfold UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0
  rw [dite_eq_left e] at h0
  set I := Finset.image f Finset.univ with hI
  have mem : ∀ i, f i ∈ I := fun i => by simp [hI]
  let σf : Fin S.card → Fin S.card := fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩
  have hσ : Function.Injective σf := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab
    simpa [σf] using this
  let σ : Equiv.Perm (Fin S.card) := Equiv.ofBijective σf hσ.bijective_of_finite
  have hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ := by
    funext i
    simp only [Function.comp, σ, Equiv.ofBijective_apply, σf]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp
  have key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) =
      (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id := by
    rw [hfg, Matrix.submatrix_submatrix]
    rfl
  rw [key, Matrix.det_permute, h0, mul_zero]
