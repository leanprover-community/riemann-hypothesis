import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

section
noncomputable section

namespace PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def HasWallD (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ R Op H, Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H

def HasWallU (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ, StripEntire M ∧ (∀ z, M z ≠ 0) ∧ HasWallD Γ K P P' c η η' β ρ fun z => M z * D z

def Triv (K₀ : Subgroup G) {K : Subgroup G} (ρ : K →* (W →L[ℂ] W)) : Prop := ∀ k : K, (k : G) ∈ K₀ → ρ k = 1

def AllRepT (K K₀ : Subgroup G) (Q : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W], (K →* (W →L[ℂ] W)) → Prop) :
    Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (ρ : K →* (W →L[ℂ] W)), Continuous ρ →
    Triv K₀ ρ → Q ρ

def TwistD : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K K₀ P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β : G → ℝ) (D : ℂ → ℂ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    (∀ k ∈ K, k ∈ K₀ → c₀ k = 1) → IsPar Γ K P c → IsPar Γ K P' c →
    AllRepT K K₀ (fun ρ => HasWallU Γ K P P' c η η' β ρ D) → AllRepT K K₀ (fun ρ => HasWallU Γ K P P' (c * c₀) η η' β ρ D)

def ScaleD : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ)
  (D : ℂ → ℂ), 0 < s → IsHt Γ K ⊤ l → HasWallU Γ K P P' c η η' β ρ D →
  HasWallU Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (fun z => D (s * z))

def TransferD : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (G' : Type) [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (Γ Q P₁ P₂ K₀ : Subgroup G) (Γ' K' P₁' P₂' K₀' : Subgroup G')
  (π : Q →* G') (ι : G' →* Q) (c₀ c : G → ℂ) (c' : G' → ℂ) (η₁ η₂ β : G → ℝ) (η₁' η₂' β' : G' → ℝ) (D : ℂ → ℂ),
  IsCompact (K' : Set G') → IsLevi Γ K Q Γ' K' π ι c₀ → IsPull Q P₁ P₁' π c₀ c c' → IsPull Q P₂ P₂' π c₀ c c' →
  IsPar Γ' K' P₁' c' → IsPar Γ' K' P₂' c' → IsHt Γ' K' P₁' η₁' → IsHt Γ' K' P₂' η₂' → IsHt Γ' K' P₂' β' →
  PullHt K Q π η₁ η₁' → PullHt K Q π η₂ η₂' → PullHt K Q π β β' → (∀ m ∈ K', m ∈ K₀' → (ι m : G) ∈ K₀) → Triv K₀ ρ →
  AllRepT K' K₀' (fun ρ' => HasWallU Γ' K' P₁' P₂' c' η₁' η₂' β' ρ' D) → HasWallU (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ D

def GalleryD : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => FirstCountableTopology G →
  ∀ (Γ S A B Q₁ Q₂ : Subgroup G) (c : G → ℂ) (h a b : G → ℝ) (N : ℝ) (Dc Da Db : ℂ → ℂ), A ≤ S → B ≤ S → A ≤ Q₁ →
  B ≤ Q₂ → IsPar Γ K S c → IsPar Γ K A c → IsPar Γ K B c → IsHt Γ K S h → IsHt Γ K Q₁ a → IsHt Γ K Q₂ (fun g => h g + b g) →
  (∃ R : ℝ, (∀ y : ℝ, R < y → Conv Γ S fun g => y * h g) ∧
    (∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) ∧
    ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) →
  HasFirst (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) ρ →
  HasWallU (Γ ⊓ Q₂) K B B c (fun g => -b g) (fun g => -b g) (fun g => -b g) ρ Dc →
  HasWallU (Γ ⊓ S) K B A c b a (fun g => N * a g - h g) ρ Da →
  HasWallU (Γ ⊓ Q₁) K A A c (fun g => h g - a g) (fun g => h g - a g) (fun g => (N - 1) * (h g - a g)) ρ Db →
  HasLast (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) h N ρ →
  HasWallU Γ K S S c h h (fun g => N * h g) ρ
    (fun y => Dc (y + 1 - N) * Da (2 * y + 1 - N) * Db y)

end PositivityTheory.RgEis
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgEis

variable {E R : Type} [Field E] [CommRing R]

namespace Ad

variable (A : Ad E R)

structure IsIdem (e : R) : Prop where
  sq : e * e = e
  σ : A.σ e = e
  O : e ∈ A.O
  φ : ∀ w, A.φ w e = 1

def k0GL (e : R) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (GL ι R) where
  carrier := {k | k ∈ A.kGL ι ∧ e • (k : Matrix ι ι R) = e • 1 ∧ e • ((k⁻¹ : GL ι R) : Matrix ι ι R) = e • 1}
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [Units.val_mul, ← smul_mul_assoc, ha.2.1, smul_mul_assoc,
      Matrix.one_mul, hb.2.1], by rw [_root_.mul_inv_rev, Units.val_mul, ← smul_mul_assoc, hb.2.2, smul_mul_assoc,
      Matrix.one_mul, ha.2.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

def unitaryIntegralLevel (e : R) (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] : Subgroup (A.U ε ι) := (A.k0GL e (ι ⊕ ι)).subgroupOf _

def ChiT (e : R) : Prop := ∀ u : Rˣ, (u : R) ∈ A.O → ((u⁻¹ : Rˣ) : R) ∈ A.O → e * u = e → A.χ u = 1

variable [TopologicalSpace R]

def MirGLU (e : R) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι), 2 ≤ Fintype.card ι → ∃ D : ℂ → ℂ,
    AllRepT (A.kGL ι) (A.k0GL e ι) fun ρ => HasWallU (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (stab R {i₀}) 1
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) ρ D

def SgU (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι] (e : R) : Prop :=
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) → ∃ D : ℂ → ℂ,
    AllRepT (A.uK ε ι) (A.unitaryIntegralLevel e ε ι) fun ρ =>
      HasWallU (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε Set.univ) (A.uH ε Set.univ)
        (fun g => (Fintype.card ι : ℝ) * A.uH ε Set.univ g) ρ D

end Ad

def LeviSU : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (e : R), A.IsIdem e →
  Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι) →
  ∃ (π : A.uQ ε (Set.univ : Set ι) →* GL ι R) (j : GL ι R →* A.uQ ε (Set.univ : Set ι)),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ) (A.ratGL ι) (A.kGL ι) π j 1 ∧
    (∀ s : Set ι, IsPull (A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (stab R s) π 1 (A.uC ε ι) (A.cGL ι)) ∧
    (∀ s : Set ι, Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι)) ∧
    (∀ s : Set ι, PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (A.uH ε s) (A.htGL s)) ∧
    ∀ m ∈ A.k0GL e ι, ((j m : A.uQ ε Set.univ) : A.U ε ι) ∈ A.unitaryIntegralLevel e ε ι

open Classical in

def LeviQU : Prop := ForAd fun {_} {R} _ _ _ _ A => ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ε : ℤˣ) (s : Set ι) (e : R), A.IsIdem e →
  Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) →
  ∃ (π : A.uQ ε s →* A.U ε (sᶜ : Set ι)) (j : A.U ε (sᶜ : Set ι) →* A.uQ ε s) (c₀ : A.U ε ι → ℂ),
    IsLevi (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε s) (A.uΓ ε _) (A.uK ε _) π j c₀ ∧
    IsPull (A.uQ ε s) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε Set.univ) π c₀ (A.uC ε ι) (A.uC ε _) ∧
    Iwa (A.uQ ε (Set.univ : Set (sᶜ : Set ι))) (A.uK ε _) ∧
    PullHt (A.uK ε ι) (A.uQ ε s) π (fun g => A.uH ε Set.univ g - A.uH ε s g) (A.uH ε Set.univ) ∧
    ∀ m ∈ A.unitaryIntegralLevel e ε (sᶜ : Set ι), ((j m : A.uQ ε s) : A.U ε ι) ∈ A.unitaryIntegralLevel e ε ι

def SgStepU : Prop := ForAd fun {_} {R} _ _ _ _ A => A.MirGL → ∀ e : R, A.IsIdem e → A.ChiT e → A.MirGLU e →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], 2 ≤ Fintype.card ι →
    (∀ (κ : Type) [Fintype κ] [DecidableEq κ], 1 ≤ Fintype.card κ → Fintype.card κ < Fintype.card ι → A.SgU ε κ e) →
    A.SgU ε ι e

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

def eSF {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) 1 + LinearMap.inr F (Ainf F) (Af F) (∑ v ∈ S, singleFin v 1)

def eCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl F)) : AE F E :=
  algebraMap (AF F) (AE F E) (eSF S)

def CMMirU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).MirGLU (eCM S)

def SgOneU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).ChiT (eCM S) →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 1 → (adCM σ χ).SgU ε ι (eCM S)

def SgAllU : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).ChiT (eCM S) →
  ∀ (ε : ℤˣ) (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι → (adCM σ χ).SgU ε ι (eCM S)

def EIdem : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S : Finset (Pl F), (adCM σ χ).IsIdem (eCM S)

def ChiS : Prop := ForCM fun {F} {_} _ _ _ _ _ σ χ => ∀ S₀ : Finset (Pl F), ∃ S, S₀ ⊆ S ∧ (adCM σ χ).ChiT (eCM S)

end PositivityTheory.RgEis
end
end
