import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def IsKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.rank = M ∧ W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def IsPerp (W : HSpace E) (x : W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V) : Prop :=
  Function.Injective ι ∧ (∀ a b, W.hD (ι a) (ι b) = W'.hD a b) ∧
    ∀ y : W.V, (∃ a, ι a = y) ↔ W.hD y x = 0

end Spaces

def IsVol (D : D7) : letI := D.host.cmStar; HSpace D.host.E → ℕ → ℕ → ℝ → Prop :=
  letI := D.host.cmStar
  fun W P Q V =>
    0 < V ∧
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal V

def Concl (D : D7) : letI := D.host.cmStar;
    HSpace D.host.E → ℕ → ℕ → ℕ → D.host.E → ℕ → ℕ → Prop :=
  letI := D.host.cmStar
  fun W M P Q β P' Q' =>
    (∃ x : W.V, W.hD x x = β) ∧
    ∀ x : W.V, W.hD x x = β →
      (∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        IsPerp W x W' ι ∧ IsKind W' (M - 1) P' Q') ∧
      ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V), IsPerp W x W' ι → W'.SigOK →
        IsKind W' (M - 1) P' Q' ∧
        ∃ V V' : ℝ, IsVol D W P Q V ∧ IsVol D W' P' Q' V' ∧
          V / V' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M

def VolumeRatio (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (M P Q : ℕ), IsKind W M P Q → 3 ≤ M →
    (1 ≤ P → Concl D W M P Q 1 (P - 1) Q) ∧ (1 ≤ Q → Concl D W M P Q (-1) P (Q - 1))

theorem IsVol.unique (D : D7) : letI := D.host.cmStar;
    ∀ (W : HSpace D.host.E) (P Q : ℕ) (V V' : ℝ), IsVol D W P Q V → IsVol D W P Q V' → V = V' := by
  intro W P Q V V' h h'
  obtain ⟨hV, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨hV', -, hall'⟩ := h'
  obtain ⟨⟨𝓕, h𝓕⟩, h1⟩ := hall μ hμ
  have h2 := (hall' μ hμ).2 𝓕 h𝓕
  exact (ENNReal.ofReal_eq_ofReal_iff hV.le hV'.le).1 ((h1 𝓕 h𝓕).symm.trans h2)


end GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
