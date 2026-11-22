module

public import Mathlib

@[expose] public section

open MvPolynomial
open scoped IsMulCommutative

namespace GlobalTheory.Wick

section Eval

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] {σ ι κ : Type*}

open scoped IsMulCommutative in
noncomputable def commEval (k : Type*) [CommSemiring k] [Algebra k A] (a : σ → A)
    (ha : ∀ i j, Commute (a i) (a j)) : MvPolynomial σ k →ₐ[k] A :=
  haveI : IsMulCommutative (Algebra.adjoin k (Set.range a)) :=
    Algebra.isMulCommutative_adjoin k (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact ha i j)
  (Algebra.adjoin k (Set.range a)).val.comp
    (aeval fun i => (⟨a i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin k (Set.range a)))

@[simp] theorem commEval_X (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (i : σ) :
    commEval k a ha (X i) = a i := by
  simp [commEval]

@[simp] theorem commEval_C (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (c : k) :
    commEval k a ha (C c) = algebraMap k A c := algHom_C _ _

variable {a : ι → A} {a' : κ → A} (ha : ∀ i j, Commute (a i) (a j))
  (ha' : ∀ i j, Commute (a' i) (a' j))

end Eval

section Divided

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : Type*}

def multiChoose (n β : σ →₀ ℕ) : ℕ := β.prod fun i e => (n i).choose e

@[simp] theorem multiChoose_zero (n : σ →₀ ℕ) : multiChoose n 0 = 1 := by simp [multiChoose]

@[simp] theorem dividedDeriv_zero : dividedDeriv R (0 : σ →₀ ℕ) =
    (1 : Module.End R (MvPolynomial σ R)) := by
  apply LinearMap.ext
  intro P
  apply MvPolynomial.ext
  intro m
  simp [coeff_dividedDeriv]

end Divided

section Contraction

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}

variable [Fintype κ]

variable [Fintype ι]

end Contraction

section Integrality

variable {R : Type*} [CommSemiring R] {ι κ : Type*}

variable [Fintype ι] [Fintype κ]

variable {A : Type*} [CommSemiring A] [Algebra A R]

end Integrality

section Fractional

open scoped nonZeroDivisors

variable {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] {ι κ : Type*} [Fintype ι] [Fintype κ]

end Fractional

section Formula

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] [Module A M]
  {ι κ : Type*}

variable [Fintype κ]

variable [Fintype ι] {a b : ι → A} {a' b' : κ → A} {γ : ι → κ → k} {v : M}

end Formula

end GlobalTheory.Wick
