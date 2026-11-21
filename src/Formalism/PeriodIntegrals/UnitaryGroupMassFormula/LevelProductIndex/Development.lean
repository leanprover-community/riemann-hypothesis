import Mathlib
import Formalism.PeriodIntegrals.LevelProdIdx

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

abbrev latA (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
      (Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  latS (F := F) (FiniteAdeleRing (𝓞 F) F)
    (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb

abbrev latV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F)
    (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb

def PLGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (O : Subring R) (n k : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (m : Fin k → Fin n → E),
    (∀ i, m i ∈ Lb) → (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) →
    ∀ y : Fin n → E ⊗[F] R,
      y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Lb ↔
        ∃ a : Fin k → R, (∀ i, a i ∈ O) ∧ y = fun j => ∑ i, m i j ⊗ₜ[F] a i

def PLInj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ v, prV (E := E) v z = 0) → z = 0

def PLDown : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    y ∈ latA F Lb → (fun j => prV (E := E) v (y j)) ∈ latV v Lb

def PLUp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Lb : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Lb →
    ∀ y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ v, (fun j => prV (E := E) v (y j)) ∈ latV v Lb) → y ∈ latA F Lb

def PLLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)),
    Module.Finite (𝓞 E) Lb →
    ∀ g ∈ levelAfL σ J Lb, ∀ v, bc (prV (E := E) v) g ∈ levelVL σ J v Lb

theorem bc_mulVec {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B)
    (g : GL (Fin n) A) (y : Fin n → A) :
    (fun j => φ (((g : Matrix (Fin n) (Fin n) A) *ᵥ y) j)) =
      ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) *ᵥ (fun j => φ (y j)) := by
  unfold bc
  funext j
  rw [RingHom.map_mulVec]
  rfl



end PI.LPI
