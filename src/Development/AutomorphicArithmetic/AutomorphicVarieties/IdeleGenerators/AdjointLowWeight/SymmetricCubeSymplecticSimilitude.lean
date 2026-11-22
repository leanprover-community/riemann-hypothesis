module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws

namespace UpperTheory.V.Sd.S3

abbrev M2 (R : Type) : Type := Matrix (Fin 2) (Fin 2) R

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

def low (x : R) : M2 R := !![1, 0; x, 1]

variable {u : R} (hu : 3 * u = 1)
include hu

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def toB {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) : Γ →* (Qbar l)ˣ :=
  (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp χ

def toC {Γ : Type} [Group Γ] {c₁ : Coef l} (h : c.O ≤ c₁.O) (χ : Γ →* c.Oˣ) : Γ →* c₁.Oˣ :=
  (Units.map (inc h).toMonoidHom).comp χ

def KillsN : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c), Ctx3 D →
    ∃ N : ℕ, 0 < N ∧ ¬ l ∣ N ∧ KillsMu N D.ξ

def SplitPrime : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    commutator (G ℚ Ω) ≤ U → ∀ M : ℕ, 0 < M → ∃ w : ℕ, w.Prime ∧ M < w ∧ w ≡ 1 [MOD M] ∧
      ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ U

def ThetaEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] →
    ∃ θ : G ℚ Ω →* (Qbar l)ˣ, θ ≠ 1 ∧ θ ^ l = 1 ∧ KillsMu w θ

def ThetaUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → ∀ θ : G ℚ Ω →* (Qbar l)ˣ,
    θ ^ l = 1 → KillsMu w θ → (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) ∧
      ∀ F : IntermediateField ℚ Ω, Dies l w F → F.fixingSubgroup ≤ θ.ker

def MuIne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ muOf l (Dec (F := F) A), s ∈ Ine (F := F) A ∧ cycZ F Ω l s = 1

def Teich : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : c.Oˣ) (m : ℕ), l.Coprime m → x ^ m = 1 → residue c.O x = 1 → x = 1

def SqrtChar : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) →
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (μ : Γ →* Oˣ), (∀ g, residue O (μ g) = 1) →
    AdicCont (maximalIdeal O) (fun g => (μ g : O)) → ∃ η : Γ →* Oˣ, (∀ g, η g ^ 2 = μ g) ∧ (∀ g, residue O (η g) = 1) ∧
      AdicCont (maximalIdeal O) (fun g => (η g : O)) ∧ ∀ g, μ g = 1 → η g = 1

def LineEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (H : Subgroup Γ) (ρ : Γ →* GL (Fin 2) (Qbar l)) (ξ : Γ →* (Qbar l)ˣ)
    (κ : Fin 2 → ↥H →* (Qbar l)ˣ), (∀ g, ‖ρ g 1 1 - 1‖ < 1 ∧ ‖ρ g 1 0‖ ≤ 1) → IsFlagOn ρ H κ → (∀ s : H, Cong (κ 0 s) (ξ s)) →
    (∃ s ∈ H, ¬ Cong (ξ s) 1) → ∃ x : Qbar l, ‖x‖ ≤ 1 ∧ ∀ s : H, ρ s 0 0 + ρ s 0 1 * x = κ 0 s ∧
      ρ s 1 0 + ρ s 1 1 * x = κ 0 s * x ∧ ρ s 1 1 - x * ρ s 0 1 = κ 1 s

def RootMem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)) (a b c d x : Qbar l), a ∈ E → b ∈ E → c ∈ E → d ∈ E →
    ‖b‖ < 1 → ‖a - d‖ = 1 → ‖x‖ ≤ 1 → c + d * x = (a + b * x) * x → x ∈ E

def CoefEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], (∀ (c : Coef l) (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E →
      ∃ c₁ : Coef l, c.O ≤ c₁.O ∧ ∀ y ∈ E, ‖y‖ ≤ 1 → y ∈ c₁.O) ∧
    ∀ (c : Coef l) (Γ : Type) [TopologicalSpace Γ] (f : Γ → c.O),
      AdicCont (maximalIdeal c.O) f ↔ Continuous fun g => (f g : PadicAlgCl l)

end UpperTheory.V.Sd.S3

end
