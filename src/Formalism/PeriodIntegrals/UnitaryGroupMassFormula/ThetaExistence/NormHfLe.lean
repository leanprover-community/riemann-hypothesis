import Formalism.PeriodIntegrals.ThGExist

section
namespace PI.ThGW

section Defs

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def kerA (A : ℝ) (a : T → I → J → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => Complex.exp ((Real.pi : ℂ) * HfG A z a)

noncomputable def poin (s A : ℝ) (La : AddSubgroup (T → I → J → ℂ)) (a : T → I → J → ℂ) :
    (T → I → J → ℂ) → ℂ :=
  fun z => ∑' x : La, alG s A (x : T → I → J → ℂ) * UG A (x : T → I → J → ℂ) (kerA A a) z

end Defs

def GaussSumm : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (ι : Type) [Fintype ι]
    (b : Module.Basis ι ℝ (T → I → J → ℂ)) (c C : ℝ), 0 < c →
    Summable (fun x : AddSubgroup.closure (Set.range b) =>
      Real.exp (-c * ‖(x : T → I → J → ℂ)‖ ^ 2 + C * ‖(x : T → I → J → ℂ)‖))

def TermBound : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ x a z : T → I → J → ℂ,
      ‖alG s A x * UG A x (kerA A a) z‖ ≤
        Real.exp (Real.pi * (Fintype.card T * Fintype.card I * Fintype.card J : ℝ) *
            (‖z‖ * ‖a‖ + ‖x‖ * ‖a‖ + ‖z‖ * ‖x‖) / A - Real.pi * ‖x‖ ^ 2 / (2 * A))

def PoinHol : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∀ a : T → I → J → ℂ, Differentiable ℂ (poin s A La a)

def PoinInv : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∀ a : T → I → J → ℂ, ∀ y ∈ La, ∀ z, alG s A y * UG A y (poin s A La a) z = poin s A La a z

def PoinNz : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La : AddSubgroup (T → I → J → ℂ), GoodLat s A La →
      ∃ a : T → I → J → ℂ, poin s A La a ≠ 0

end PI.ThGW
end

section
namespace PI.ThGW

namespace Hol

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

lemma hf_add_left (A : ℝ) (z z' w : T → I → J → ℂ) :
    HfG A (z + z') w = HfG A z w + HfG A z' w := by
  simp only [HfG, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma hf_smul_left (A : ℝ) (c : ℂ) (z w : T → I → J → ℂ) :
    HfG A (c • z) w = c * HfG A z w := by
  simp only [HfG, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

noncomputable def hl (A : ℝ) (v : T → I → J → ℂ) : (T → I → J → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => HfG A z v
      map_add' := fun z z' => hf_add_left A z z' v
      map_smul' := fun c z => by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply] }

end Hol

end PI.ThGW
end
