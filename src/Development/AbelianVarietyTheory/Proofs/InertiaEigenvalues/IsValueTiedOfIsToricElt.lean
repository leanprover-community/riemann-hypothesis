import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

def RatioConj : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ →
    ∀ (Ω : Type) [Field Ω] [Algebra H.K Ω] [IsAlgClosure H.K Ω] (j : Ω →+* ℂ) (τ₀ : I),
    (∀ x : H.K, j (algebraMap H.K Ω x) = φ τ₀ x) →
    ∀ art : Ideles H.K →* Gab H.K Ω, IsGlobalArtin art →
    ∀ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ → T₀ ≠ 0 →
    ∀ Q : Finset (HeightOneSpectrum (OF H.E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → Finite (PicO (condQ 𝔣 Q)) →
    ∀ T : PicO (condQ 𝔣 Q) → ℂ, (∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q)) →
    ∃ ρ : (PicO (condQ 𝔣 Q) →* Ωˣ) → Ω,
      (∀ ψ, j (ρ ψ) = (∑ᶠ q, (j (ψ q))⁻¹ * T q) / T₀) ∧
      ∀ g : G H.K Ω, (∀ (x : Ω) (τ : I) (y : H.E), j x = φ τ y → g x = x) → (∀ (x : Ω) (y : (Af H.E)ˣ), j x = lamF s χ y → g x = x) →
        ∀ t : (Af H.K)ˣ, art (finIdele H.K t) = toAb H.K Ω g⁻¹ → ∀ ψ : PicO (condQ 𝔣 Q) →* Ωˣ,
          g (ρ ψ) = (g (ψ (QuotientGroup.mk (upIdele H.K H.E t))))⁻¹ * ρ ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def setTh (th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := th }

def IsValueCharAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E),
    IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1

def IsValueTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsValueCharAt X i (atSide X (X.sideL i lam) ι) lam s

def IsGalTied : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ (e : FractionRing (X.O0 i) →+* Qbar (X.l i)) (ι : Qbar (X.l i) ≃+* ℂ)
    (art : Ideles D.host.E →* Gab D.host.E N.Om), IsGlobalArtin art ∧
    (∀ z : ℤ_[X.l i], e (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
      algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])) ∧
    (∀ x : D.LL0, ι (e (X.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s →
      ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
        (n : (D.host.E →+* ℂ) → ℤ) (r : G D.host.E N.Om →* (X.O0 i)ˣ),
        IsHostDatum D.host φ s κ 𝔣 χ ∧ (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
        GlobalTheory.GalChar.IsGal art e (GlobalTheory.GalChar.sideIso ι (X.sideL i lam)) χ n r ∧
        X.lamG i lam = (Units.map (algebraMap (X.O0 i) (X.O i)).toMonoidHom).comp r

variable {X}


theorem toBar_algebraMap (i : X.Tw) (a : X.O0 i) :
    toBar X i (algebraMap (X.O0 i) _ a) = algebraMap (X.O i) (Kbar X i) (algebraMap (X.O0 i) (X.O i) a) := by
  rw [toBar, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl


end GlobalTheory.ToricRational
