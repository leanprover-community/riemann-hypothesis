module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp

@[expose] public section

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

section K3

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])
    (DelF : DelTy X E) (hDel : DelDeg X E DelF)

theorem condition_iff_additive_maps (D : Formalism.BasicNotions.D7) :
    Formalism.MainNotions.FormalGroupSystem.adm5 D X (pendOf X E hfin hst be ThF DelF hDel) ↔
      ∀ v, ∀ j < X.mm, letI := algKfC E; XiEx X ℂ_[p] ThF v j := by
  let _ := algKfC E
  constructor
  · intro h v j hj
    exact ⟨_, h v j hj⟩
  · intro h v j hj
    exact xiOf_spec X ℂ_[p] ThF (h v j hj)

end K3

section Rename

variable (X : Sys p) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def kapOf (j : ℕ) (z : X.ZA j) : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1) :=
  (pos ⟨z.1, z.2.1⟩, Fin.cast (rank_eq X (j + 1)).symm z.2.2.2, Fin.cast (rank_eq X j).symm z.2.2.1)

def thFOf (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : MvPowerSeries (X.ZA j) ℂ_[p] :=
  resV (kapOf X pos j) (F j La La')

theorem kapOf_injective (j : ℕ) : Function.Injective (kapOf X pos j) := by
  rintro ⟨v, s, a, b⟩ ⟨v', s', a', b'⟩ h
  simp only [kapOf, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.cast_inj] at h
  obtain ⟨h1, h2, h3⟩ := h
  cases h1
  subst h2 h3
  rfl

end Rename

def Compat (G : GAtP p) (E : CEmb G) (rd : ∀ v, G.P.W v →+* WW p) : Prop :=
  ∀ (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v),
    E.iK (G.P.ι v ((G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x))) =
      k0ToC p (algebraMap (WW p) (K0 p) ((sigW p)^[s] (rd v x)))

section Conc

variable {n : ℕ} (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

def rdW (p : ℕ) [Fact p.Prime] (n : ℕ) : WQ p n →+* WW p := (gWW p n).comp (jW p n)

end Conc

end Formalism.L2.G.Pend
