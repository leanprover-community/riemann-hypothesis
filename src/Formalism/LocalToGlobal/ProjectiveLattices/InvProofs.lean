import Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply

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
