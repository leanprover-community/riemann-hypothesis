module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

structure Dat (A : Type) [CommRing A] (n : Type) (r : ℕ) where
  σA : A →+* A
  JA : Matrix n n A
  e : Fin r → n → A
  f : Fin r → n → A
  z : n → A
  tz : A

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable (D : Dat A n r)

def h (x y : n → A) : A := hform D.σA D.JA x y

def hL (x : n → A) : (n → A) →ₗ[A] A where
  toFun y := D.h x y
  map_add' y y' := by
    simp only [h, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [h, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_add_right (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by
  simpa only [hL_apply] using (D.hL x).map_add y y'

theorem h_smul_right (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  simpa only [hL_apply, smul_eq_mul] using (D.hL x).map_smul c y

theorem h_sub_right (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  simpa only [hL_apply] using (D.hL x).map_sub y y'

theorem h_zero_right (x : n → A) : D.h x 0 = 0 := by
  simpa only [hL_apply] using (D.hL x).map_zero

theorem h_add_left (x x' y : n → A) : D.h (x + x') y = D.h x y + D.h x' y := by
  simp only [h, hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem h_smul_left (x y : n → A) (c : A) : D.h (c • x) y = D.σA c * D.h x y := by
  simp only [h, hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

structure Hyp : Prop where
  σσ : ∀ x, D.σA (D.σA x) = x
  herm : ∀ i j, D.σA (D.JA j i) = D.JA i j
  ee : ∀ a b, D.h (D.e a) (D.e b) = 0
  ff : ∀ a b, D.h (D.f a) (D.f b) = 0
  ef : ∀ a b, D.h (D.e a) (D.f b) = if a = b then 1 else 0
  ez : ∀ a, D.h (D.e a) D.z = 0
  fz : ∀ a, D.h (D.f a) D.z = 0
  zz : D.tz * D.h D.z D.z = 1

variable {D}

theorem h_symm (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fe (H : D.Hyp) (a b : Fin r) : D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [h_symm H, H.ef b a]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, Ne.symm hab]

variable (D)

def pX : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.f a)).smulRight (D.e a)

def pXv : (n → A) →ₗ[A] (n → A) := ∑ a, (D.hL (D.e a)).smulRight (D.f a)

theorem pX_apply (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply]

theorem pXv_apply (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply]

variable {D}

end Dat

end PI.VolSemiDirect.W.PG
