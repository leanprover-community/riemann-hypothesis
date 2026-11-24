module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem isField_pi_fin_iff {k : ℕ} (A : Fin k → Type) [∀ i, CommRing (A i)]
    [∀ i, Nontrivial (A i)] : IsField (∀ i, A i) ↔ k = 1 ∧ ∀ i, IsField (A i) := by
  constructor
  · intro h

    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
      · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
        have hk0 : k = 0 := by omega
        subst hk0
        exact absurd (funext fun i => i.elim0) hab
      · exact heq
      · let i₀ : Fin k := ⟨0, by omega⟩
        let i₁ : Fin k := ⟨1, hgt⟩
        have hne : i₁ ≠ i₀ := by
          intro hij
          have := congrArg Fin.val hij
          simp [i₀, i₁] at this
        have hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0 := by
          intro hx
          have := congrFun hx i₀
          simp at this
        obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
        have := congrFun hy i₁
        rw [Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply] at this
        exact absurd this zero_ne_one
    refine ⟨hk, ?_⟩
    subst hk
    intro i
    have hdef : IsField (A default) := (RingEquiv.piUnique A).symm.toMulEquiv.isField h
    exact (Unique.eq_default i).symm ▸ hdef
  · rintro ⟨rfl, h⟩
    exact (RingEquiv.piUnique A).toMulEquiv.isField (h default)

theorem tensorFieldIff : TensorFieldIff := by
  intro F E _ _ _ _ P _ _ k K _ _ ⟨e⟩

  let φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm F _ E).trans
        ((Algebra.TensorProduct.piRight F F E K).trans
          (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))

  have : ∀ i, Nontrivial (K i ⊗[F] E) := fun i =>
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E)
      (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective
  rw [φ.toRingEquiv.toMulEquiv.isField_congr]
  exact isField_pi_fin_iff _

end GlobalTheory.RegSS
