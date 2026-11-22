module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def segSum (rc : IrrGL (k := w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E))) : WD h :=
  sumList (l.map fun Δ =>
    ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))

section Transport

def RepRel {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (x : IrrGL (k := k)) (x' : IrrGL (k := k')) : Prop :=
  ∃ (n : ℕ) (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V),
    x = cls π ∧ x' = cls π' ∧ ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)

variable {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

def WeilRel (φ : Ω ≃+* Ω') (σ : Weil h) (σ' : Weil h') : Prop :=
  ∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)

def WDRel (φ : Ω ≃+* Ω') (y : WD h) (y' : WD h') : Prop :=
  ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
    b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), WeilRel φ σ σ' → b.ρ σ = b'.ρ σ'

variable (A A' w w') in
structure PlaceIso (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E') : Prop where

  mem : ∀ z, φ z ∈ A' ↔ z ∈ A

  ext : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)

  cont : Continuous i

  loc : ∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)

end Transport

end GlobalTheory.LocLanglands

end
