module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

attribute [instance] JetRing.cr JetRing.alg

section Alg

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

end Alg

abbrev FR (E : Type) [Field E] : Type := maximalRealSubfield E

section Cx

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

variable {φ : I → E →+* ℂ} {L : Set E} {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)}

end Cx

def IsEis {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) (k : ℕ) (G : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  (k ≠ 2 → ∀ z ∈ halfSpace F, HasSum (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z) (G z)) ∧
    (k = 2 → ∃ H, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsContinuation 𝔞 𝔟 H ∧ G = H 0)

def EisExp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∃ G, IsEis 𝔞 𝔟 (2 * s) G ∧ DifferentiableOn ℂ G (halfSpace F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 (2 * s) G

def JetInt : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + ((∑ i, κ i : ℕ) : ℝ) * c_vp 𝔣 l)
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))

end GlobalTheory.LatJet
