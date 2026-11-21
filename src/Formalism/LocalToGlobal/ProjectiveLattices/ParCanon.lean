import Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply
import Formalism.LocalToGlobal.ProjectiveLattices.DatumOfRecordSignature

section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


def RdUIndep (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ →
    ∀ (U U' : Unf (Q.Xo j) Q.c σ D.R.r), IsUnf U → IsUnf U' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (Q.Xo j) Q.c a n,
      (rdU U f ∈ holSub U.X (laU U a n) ↔ rdU U' f ∈ holSub U'.X (laU U' a n)) ∧
      (rdU U f ∈ holSub U.X (laU U a n) →
        supN U.X (laU U a n) (rdU U f) = supN U'.X (laU U' a n) (rdU U' f))

def L2Independence (D : D7) : Prop :=
  ∀ (Q : Par D) (j : ℕ) (U U' : ∀ σ : Q.c.F →+* ℂ, Unf (Q.Xo j) Q.c σ D.R.r),
    (∀ σ, GoodEmb Q.c σ → IsUnf (U σ)) → (∀ σ, GoodEmb Q.c σ → IsUnf (U' σ)) →
    ∀ (σ : Q.c.F →+* ℂ), GoodEmb Q.c σ → ∀ (V : HSp D), V = D.sp.W j → ∀ (Kf : Subgroup (GA D V)),
      IsLevelK V (D.host.g 0 * D.host.g 1) Kf → FinVol V →
    ∀ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (dict' : GA D V → Σ k, Frame ((U' σ).X k).Ψ D.R.r)
      (mu mu' : GA D V → ℂ),
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr) →
      (∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict' Kf th hr) →
      MuUnit V dict mu → MuUnit V dict' mu' → Continuous mu → Continuous mu' →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (hl : JMemL2 V σ (rdC U σ a n) dict mu) (hl' : JMemL2 V σ (rdC U' σ a n) dict' mu')
      (f : Rul (Q.Xo j) Q.c), f ∈ cusp (Q.Xo j) Q.c U a n → f ∈ cusp (Q.Xo j) Q.c U' a n →
      l2C U σ V dict mu (xiR D) a n hl f = l2C U' σ V dict' mu' (xiR D) a n hl' f




end Formalism.L2.Pj
end
end

section
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
end
end
