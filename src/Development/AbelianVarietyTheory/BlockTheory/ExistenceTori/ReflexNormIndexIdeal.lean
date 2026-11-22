module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def reflexNorm (γ : E) : c.F := ∏ σ : E →+* ℂ, embF c σ γ ^ Dw.mult σ

def reflexIdeal (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 c.F) :=
  ∏ σ : E →+* ℂ, 𝔞.map (RingOfIntegers.mapRingHom (embF c σ)) ^ Dw.mult σ

def IsBe (𝔞 : Ideal (𝓞 E)) (β : c.F) : Prop :=
  (∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c 𝔞) ∧
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)

theorem isBe_top : IsBe Dw c ⊤ 1 :=
  ⟨⟨1, rfl, by
    simp only [reflexIdeal, Ideal.map_top, Ideal.span_singleton_one]
    simp [← Ideal.one_eq_top]⟩, fun s => by simp⟩

variable {Dw c}

variable (Dw c)

end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
