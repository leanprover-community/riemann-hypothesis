import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem frobQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ x : Qr p r, (⇑(frobQ p r))^[r] x = x := by
  intro p _ r hr x
  have h : (⇑(frobQ p r) : Qr p r → Qr p r) = ⇑(GlobalTheory.LKLoc.frobR p (Q0 p) r) := rfl
  rw [h]
  exact GlobalTheory.LKLoc.frobR_iterate_self p (Q0 p) (by infer_instance) r hr x

end GlobalTheory.LKRes
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem tensorMap_id_iterate_eq_self {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : B →ₐ[R] B) (r : ℕ) (hf : ∀ b, (⇑f)^[r] b = b) (x : A ⊗[R] B) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id R A) f))^[r] x = x := by
  set e := Algebra.TensorProduct.map (AlgHom.id R A) f
  have ht : ∀ k (a : A) (b : B), (⇑e)^[k] (a ⊗ₜ[R] b) = a ⊗ₜ[R] (⇑f)^[k] b := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [e]
  have hadd : ∀ k (x y : A ⊗[R] B), (⇑e)^[k] (x + y) = (⇑e)^[k] x + (⇑e)^[k] y := by
    intro k x y
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  have hzero : ∀ k, (⇑e)^[k] (0 : A ⊗[R] B) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  induction x using TensorProduct.induction_on with
  | zero => exact hzero r
  | tmul a b => rw [ht, hf]
  | add x y hx hy => rw [hadd, hx, hy]

theorem sigKQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ),
    0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  intro p _ K r hr x
  exact tensorMap_id_iterate_eq_self (A := K) (frobQ p r) r (frobQ_iterate_self p r hr) x

end GlobalTheory.LKRes

example : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := GlobalTheory.LKRes.sigKQ_iterate_self
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKRes.sigKQ_iterate_self | exact GlobalTheory.LKRes.sigKQ_iterate_self | (intros; apply GlobalTheory.LKRes.sigKQ_iterate_self; all_goals assumption)
end

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
end
