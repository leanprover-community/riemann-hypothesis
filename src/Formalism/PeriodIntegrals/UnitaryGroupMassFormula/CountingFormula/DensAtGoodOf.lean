import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocDens : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) η
            (Module.finrank E V) (Fintype.card ι) 0

def ETwo : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E),
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap

def LocDensSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1
            (Module.finrank E V) (Fintype.card ι) 0

def LocDensField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
            (Module.finrank E V) (Fintype.card ι) 0


theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm

theorem ga_herm (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (Z : MatZ D) (a b) :
    Ga (Tn u) (Tn u') Z b a = star (Ga (Tn u) (Tn u') Z a b) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Ga, Matrix.fromBlocks, Matrix.conjTranspose_apply, and_comm] <;> split_ifs <;> simp [Tn]





end PI.UnitaryGroupMassFormula.CntFormula
