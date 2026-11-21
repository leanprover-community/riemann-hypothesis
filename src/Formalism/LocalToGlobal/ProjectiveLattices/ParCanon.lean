import Formalism.LocalToGlobal.ProjectiveLattices.InvProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)





def ModTr (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T') (j : ℕ), InR D j →
    T.Q.H = T'.Q.H → HEq T.Q.l T'.Q.l → HEq T.Q.c T'.Q.c → HEq (T.Q.Dw j) (T'.Q.Dw j) →
    HEq T.Q.eO T'.Q.eO →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def ParTrC (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def INVC (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsM T) (h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h h' j fe Φ pl




end Formalism.L2.Pj
