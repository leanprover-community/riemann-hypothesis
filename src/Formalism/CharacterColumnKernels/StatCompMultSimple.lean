import Formalism.CharacterColumnKernels.StatementMF

section
open Classical

noncomputable section

namespace Formalism.NG

universe u v

section Mult
variable (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

abbrev csFactor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type u :=
  s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype

def csMult (s : CompositionSeries (Submodule R M)) (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => Nonempty (csFactor R M s i ≃ₗ[R] S)).card

def IsFullSeries (s : CompositionSeries (Submodule R M)) : Prop := s.head = ⊥ ∧ s.last = ⊤

def compMult (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  if h : ∃ s : CompositionSeries (Submodule R M), IsFullSeries R M s then
    csMult R M (Classical.choose h) S
  else 0

end Mult

def StatCsMultIndep : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s₁ s₂ : CompositionSeries (Submodule R M)),
    IsFullSeries R M s₁ → IsFullSeries R M s₂ → csMult R M s₁ S = csMult R M s₂ S

def StatCompMultEq : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s : CompositionSeries (Submodule R M)),
    IsFullSeries R M s → compMult R M S = csMult R M s S

def StatEpsMult : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (epsImg O (M := M) ε) = compMult Λ M S

def StatEpsMultHom : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε → [SMulCommClass Λ O (EpsDual O Λ (KO O) ε)] →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (M →ₗ[Λ] EpsDual O Λ (KO O) ε) = compMult Λ M S

end Formalism.NG
end
end

section
open Classical

noncomputable section

namespace Formalism.NG

universe u v w

def StatCompMultAdd : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S], IsFiniteLength R M → ∀ N : Submodule R M,
    compMult R M S = compMult R N S + compMult R (M ⧸ N) S

def StatCompMultSimple : Prop :=
  ∀ (R : Type*) [Ring R] (T : Type u) [AddCommGroup T] [Module R T] (S : Type v) [AddCommGroup S]
    [Module R S], IsSimpleModule R T →
    compMult R T S = if Nonempty (T ≃ₗ[R] S) then 1 else 0

def StatCompMultCongr : Prop :=
  ∀ (R : Type*) [Ring R] (M M' : Type u) [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (S : Type v) (S' : Type w) [AddCommGroup S] [Module R S] [AddCommGroup S']
    [Module R S'], (M ≃ₗ[R] M') → (S ≃ₗ[R] S') → compMult R M S = compMult R M' S'

def StatEpsCount : Prop :=
  ∀ (O Λ : Type*) (S : Type v) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
    [AddCommGroup S] [Module Λ S] (ε : Λ), IsIdempotentElem ε → IsSimpleModule Λ S →
    (∃ s : S, ε • s ≠ 0) →
    (∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ) →
    (∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ) →
    ∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0

def StatEpsMultCount : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
    [AddCommGroup M] [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S]
    [Module Λ S] (ε : Λ), IsIdempotentElem ε → IsSimpleModule Λ S → (∃ s : S, ε • s ≠ 0) →
    (∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ) →
    (∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ) →
    IsFiniteLength Λ M →
    Module.length O (epsImg O (M := M) ε) = compMult Λ M S

def StatFinLenIff : Prop :=
  ∀ (O Λ M : Type*) [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ] [Module.Finite O Λ]
    [AddCommGroup M] [Module Λ M] [Module O M] [IsScalarTower O Λ M],
    IsFiniteLength Λ M ↔ IsFiniteLength O M

end Formalism.NG
end
end
