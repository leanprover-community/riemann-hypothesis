import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def IsCMUnramified : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧
    ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.ramificationIdx (𝓞 F) = 1

def locIntegers (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E) :=
  integralClosure _ _

variable {F E}

def baseGram (R : Type*) [Field R] [Algebra F R] {M : ℕ} (h : HermitianForm F E (Fin M → E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (gram h.toSesq (Pi.basisFun E (Fin M))).map
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)

def matForm (R : Type*) {A : Type*} [Field R] [CommRing A] [Algebra R A]
    [Algebra.IsQuadraticExtension R A] {ι : Type*} [Fintype ι] (G : Matrix ι ι A)
    (x y : ι → A) : A :=
  ∑ i, ∑ j, conj R A (x i) * G i j * y j

def signVector (A : Type*) [Ring A] (M p : ℕ) : Fin M → A :=
  fun i => if (i : ℕ) < p then 1 else -1

def HasSignatureAt {M : ℕ} (h : HermitianForm F E (Fin M → E)) (w : InfinitePlace F)
    (p q : ℕ) : Prop :=
  p + q = M ∧
    IsCongr (conjHom w.Completion (w.Completion ⊗[F] E)) (baseGram w.Completion h)
      (diagonal (signVector (w.Completion ⊗[F] E) M p))

variable (v : HeightOneSpectrum (𝓞 F))

def IsLocLattice {M : ℕ}
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (v.adicCompletion F ⊗[F] E)
    (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = ⊤

def IsSelfDualAt {M : ℕ} (h : HermitianForm F E (Fin M → E))
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  IsLocLattice v L ∧
    ∀ x, x ∈ L ↔
      ∀ y ∈ L, matForm (v.adicCompletion F) (baseGram (v.adicCompletion F) h) x y ∈
        locIntegers F E v

def IsGlobalLattice {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin M → E)) = ⊤

def latticeAt {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) :=
  Submodule.span _ ((fun x i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) '' (Λ : Set (Fin M → E)))

end Objects

section Statements

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def SelfDualHermitianExists.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ((∃ h : HermitianForm F E (Fin M → E), (∀ τ, HasSignatureAt h τ (p τ) (q τ)) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) ↔
        Even (∑ τ, q τ))

def SelfDualHermitianUnique.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ∀ h h' : HermitianForm F E (Fin M → E),
        (∀ τ, HasSignatureAt h τ (p τ) (q τ)) → (∀ τ, HasSignatureAt h' τ (p τ) (q τ)) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L', IsSelfDualAt v h' L') →
        h.Isometric h'

def SelfDualHermitianLocal.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h h' : HermitianForm F E (Fin M → E),
      ∀ (v : HeightOneSpectrum (𝓞 F)) (L L' : Submodule (locIntegers F E v)
          (Fin M → v.adicCompletion F ⊗[F] E)),
        IsSelfDualAt v h L → IsSelfDualAt v h' L' →
        ∃ P : Matrix (Fin M) (Fin M) (v.adicCompletion F ⊗[F] E), IsUnit P.det ∧
          (P.map (conjHom (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)))ᵀ *
              baseGram (v.adicCompletion F) h' * P = baseGram (v.adicCompletion F) h ∧
          (fun x => P *ᵥ x) '' (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = L'

def SelfDualHermitianGlobalLattice.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h : HermitianForm F E (Fin M → E),
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
      ∃ Λ : Submodule (𝓞 E) (Fin M → E), IsGlobalLattice Λ ∧
        ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt v h (latticeAt v Λ)

end Statements

section Inhabitants

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

abbrev unitForm (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (M : ℕ) : HermitianForm F E (Fin M → E) :=
  diagForm (E := E) fun _ : Fin M => (1 : Fˣ)




variable (v : HeightOneSpectrum (𝓞 F))


def stdLatticeAt (M : ℕ) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) where
  carrier := {x | ∀ i, x i ∈ locIntegers F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
    exact mul_mem c.2 (hx i)






def stdLattice (M : ℕ) : Submodule (𝓞 E) (Fin M → E) where
  carrier := {x | ∀ i, IsIntegral ℤ (x i)}
  add_mem' hx hy i := (hx i).add (hy i)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx i)

theorem single_mem_stdLattice {M : ℕ} (i : Fin M) : Pi.single i (1 : E) ∈ stdLattice (E := E) M := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same]; exact isIntegral_one
  · rw [Pi.single_eq_of_ne hj]; exact isIntegral_zero





end Inhabitants

end GroundTheory.Heights₂.Theta
