import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Integrals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def PtsIntegrable {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  (∃ L : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P L) ∧
    ∀ L : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P L →
      Integrable (fun y : Fin e → ℂ => ∑ᶠ w ∈ fibre P L y, sheetDensity P L φ g y w)

end Integrals

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D)
  {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
  {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd))

def Ties : Prop :=
  S.IsTied ∧ S'.IsTied ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), S'.ref.h z = S.ref.h z

def CuspWeightDefined : Prop :=
  ∀ z ∈ D.Xo, BddAbove {x : ℝ | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧
    x = -Real.log (Cd.Nz z I)}

def MeanDefined : Prop :=
  PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) (fun _ => 1) ∧ 0 < degMu H ∧
    PtsIntegrable (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight

def SmoothAtSmallScale (B : ℕ) : Prop :=
  (∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg H S B t)) ∧
    ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ), IsSmoothHerm (MUc H S' B p q t')

def RegBoundAt (B : ℕ) (a : ℝ) (p q : ℕ) (t' : ℝ) : Prop :=
  ((D.n : ℝ) + 1) * (a - (p : ℝ) / (q : ℝ) * D.KA) * geomDegMUc H S' B p q t' ≤ topMUc H S' B p q t'

def RegBound (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ᶠ t' in 𝓝[>] (0 : ℝ), RegBoundAt H Cd S' B a p q t'

def RegBoundUnit (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∀ t' : ℝ, 0 < t' → t' ≤ 1 → RegBoundAt H Cd S' B a p q t'

def LimitBound (B : ℕ) (a : ℝ) : Prop :=
  ((D.n : ℝ) + 1) * (a - meanU H Cd / 2) * degMu H ≤ arLim H S B



end Clauses

def StokesLimit : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D)
    (O abelian₂ : Type) [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)),
    Ties H Cd S S' → CuspWeightDefined Cd → MeanDefined H Cd →
    ∀ (B : ℕ) (a : ℝ), 4 * D.f + 2 ≤ B → SmoothAtSmallScale H Cd S S' B → ArLimExists H S B →
      RegBound H Cd S' B a → LimitBound H Cd S B a

def StokesLimitUnguarded : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D)
    (O abelian₂ : Type) [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)),
    S.IsTied → S'.IsTied →
    ∀ (B : ℕ) (a : ℝ), 4 * D.f + 2 ≤ B → ArLimExists H S B →
      RegBound H Cd S' B a → LimitBound H Cd S B a


example (II : IntersectionSystem) (hII) :
    Ties (Line.lineHodge II hII) (Line.gaussCusp II hII) (Line.lineRegT II hII) (Line.lineBRegC II hII) ∧
      CuspWeightDefined (Line.gaussCusp II hII) := by
  refine ⟨⟨Line.lineRegT_tied II hII, Line.lineBRegC_tied II hII, fun _ _ => rfl⟩, fun z _ => ⟨0, ?_⟩⟩
  rintro x ⟨I, hI, -, hiso, -⟩
  exact absurd ((Submodule.eq_bot_iff I).2 fun v hv => Line.eq_zero_of_isIsoSub hiso hv) hI

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.StokesLimitBound
