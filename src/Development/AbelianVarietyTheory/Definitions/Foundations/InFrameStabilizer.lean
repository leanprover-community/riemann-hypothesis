module

public import Mathlib

@[expose] public section

noncomputable section

namespace GlobalTheory.SgAlg

variable {E : Type} [CommRing E]

def IsQA (σ : E →+* E) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∃ x, σ x ≠ x) ∧ IsReduced E ∧ IsUnit (2 : E) ∧
    ∀ x, σ x = x → x ≠ 0 → IsUnit x

def cT (σ : E →+* E) {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map σ).transpose

def IsHermU (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Prop := cT σ J = J ∧ IsUnit J.det

def form (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  dotProduct (fun i => σ (y i)) (J.mulVec x)

def pairM (σ : E →+* E) {n : ℕ} {a b : Type} (J : Matrix (Fin n) (Fin n) E)
    (P' : Matrix (Fin n) b E) (P : Matrix (Fin n) a E) : Matrix a b E := cT σ P * J * P'

def IsUn (σ : E →+* E) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E) : Prop := cT σ g * J * g = J

def Free {n : ℕ} {a : Type} [Fintype a] [DecidableEq a] (P : Matrix (Fin n) a E) : Prop :=
  ∃ L : Matrix a (Fin n) E, L * P = 1

end GlobalTheory.SgAlg
