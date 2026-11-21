import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.SameUpToScalars

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField IsDedekindDomain MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SDHerm (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm G x y)

def SDTrace (ξ : E) (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, EFf ξ G x y = k) ∧ ∀ φ : L →+ ℤ, ∃ x ∈ L, ∀ y : L, (φ y : ℚ) = EFf ξ G x y

def SDPair (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (G' : Matrix (Fin r) (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (SDHerm G L ∧ SDHerm G' L') ∨ ∃ ξ : E, ξ ≠ 0 ∧ cc ξ = -ξ ∧ SDTrace ξ G L ∧ SDTrace ξ G' L'

end defs

def Isotropic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 3 ≤ r → 0 < X.p0 → X.p0 < r →
    ∃ e : Fin r → E, e ≠ 0 ∧ herm X.Gm e e = 0

def DualTransport : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E) (a : GL (Fin r) E)
    (L' : Submodule (𝓞 E) (Fin r → E)),
    (a : Matrix (Fin r) (Fin r) E)ᵀ * G * (a : Matrix (Fin r) (Fin r) E).map (ccH E) = G' → IsLat L' →
    ∃ aL' : Submodule (𝓞 E) (Fin r → E), IsLat aL' ∧ (∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ aL') ∧
      (SDHerm G' L' → SDHerm G aL') ∧ ∀ ξ, SDTrace ξ G' L' → SDTrace ξ G aL'

def LocalToAdelic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (L L' : Submodule (𝓞 E) (Fin r → E)), IsLat L → IsLat L' →
    (∃ γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), GL (Fin r) (GlobalTheory.SelfDualGenus.LocAlg v),
      (∀ v, GlobalTheory.SelfDualGenus.IsLocalIsometry v G L' G L (γ v)) ∧ {v | γ v ≠ 1}.Finite) →
    AdGenus (IsCMField.complexConj E) G L L'

def EqVolSD : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (r : ℕ) (X X' : Data E r) (L L' : Submodule (𝓞 E) (Fin r → E)) (𝔞 : Ideal (𝓞 E)),
    X.Ψ = X'.Ψ → X.p0 = X'.p0 → 3 ≤ r → 0 < X.p0 → X.p0 < r → IsLat L → IsLat L' → SDPair X.Gm L X'.Gm L' →
    𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    SameOrbits X X.Γ (levelGrp (ccH E) X.Gm L 𝔞) → SameOrbits X' X'.Γ (levelGrp (ccH E) X'.Gm L' 𝔞) →
    ∀ (x : Frame X.Ψ r) (x' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))),
      IsOrth X x → IsOrth X' x' → IsFundSet X x FF → IsFundSet X' x' FF' → muF X x FF = muF X' x' FF'


end PositivityTheory.EqVol
