import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.IsIsotropicHermitianSetting

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

abbrev ccH (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E).toRingHom

def FundFor (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ, ∀ b ∈ Bor X.Ψ r, cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x0 z') b)


def FreeOn (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ γ ∈ Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ x = rmul x b → γ = 1

def SameUpToScalars (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  (∀ γ ∈ Γ, ∃ s : Eˣ, ∃ γ' ∈ Γ', (γ' : Matrix (Fin r) (Fin r) E) = (s : E) • (γ : Matrix (Fin r) (Fin r) E)) ∧
  ∀ γ' ∈ Γ', ∃ s : Eˣ, ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = (s : E) • (γ' : Matrix (Fin r) (Fin r) E)

def SameOrbits (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)) : Prop :=
  ∀ x ∈ X.dom, ∀ y ∈ X.dom, (∃ γ ∈ Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)) ↔
    ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)

end defs

def VolOfIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ₁ Γ₂ : Subgroup (GL (Fin r) E))
    (x₁ x₂ : Frame X.Ψ r) (F₁ F₂ : Set (V (nd X))),
    Γ₁ ≤ uGrp (ccH E) X.Gm → Γ₂ ≤ uGrp (ccH E) X.Gm → FreeOn X Γ₁ → FreeOn X Γ₂ → EqIdx Γ₁ Γ₂ →
    IsOrth X x₁ → IsOrth X x₂ → FundFor X Γ₁ x₁ F₁ → FundFor X Γ₂ x₂ F₂ → muF X x₁ F₁ = muF X x₂ F₂

def Transport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (Γ' : Subgroup (GL (Fin r) E)) (x' : Frame X'.Ψ r) (F' : Set (V (nd X'))),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    IsOrth X' x' → FreeOn X' Γ' → FundFor X' Γ' x' F' →
    FreeOn X (conjBy a Γ') ∧ ∃ (x : Frame X.Ψ r) (F : Set (V (nd X))),
      IsOrth X x ∧ FundFor X (conjBy a Γ') x F ∧ muF X x F = muF X' x' F'

def ScalarSwap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    SameUpToScalars Γ Γ' →
    (∀ γ ∈ Γ', (∃ s : E, (γ : Matrix (Fin r) (Fin r) E) = s • (1 : Matrix (Fin r) (Fin r) E)) → γ = 1) →
    FreeOn X Γ → FreeOn X Γ' ∧ ∀ x0 FF, FundFor X Γ x0 FF → FundFor X Γ' x0 FF

def ScalarsOfOrbits : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Γ Γ' : Subgroup (GL (Fin r) E)),
    Γ ≤ uGrp (ccH E) X.Gm → Γ' ≤ uGrp (ccH E) X.Gm → SameOrbits X Γ Γ' → SameUpToScalars Γ Γ'

def LevelFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (c : E ≃ₐ[F] E)
    (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) (𝔞 : Ideal (𝓞 E)), IsLat Λ → IsUnit J.det →
    (Neat c 𝔞 → ∀ γ ∈ levelGrp c.toRingHom J Λ 𝔞,
      (∃ s : E, (γ : Matrix (Fin N) (Fin N) E) = s • (1 : Matrix (Fin N) (Fin N) E)) → γ = 1) ∧
    ∀ (J₀ : Matrix (Fin N) (Fin N) E) (a : GL (Fin N) E) (Λ₀ : Submodule (𝓞 E) (Fin N → E)),
      (a : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom = J →
      (∀ x, x ∈ Λ ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ Λ₀) →
      conjBy a (levelGrp c.toRingHom J Λ 𝔞) = levelGrp c.toRingHom J₀ Λ₀ 𝔞

def EqVolFD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E)
    (L L' aL' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 →
    (a : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = X'.Gm →
    (∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0) →
    IsLat L → IsLat L' → IsLat aL' → (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') →
    AdGenus (IsCMField.complexConj E) X.Gm L aL' → 𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'



end PositivityTheory.EqVol
