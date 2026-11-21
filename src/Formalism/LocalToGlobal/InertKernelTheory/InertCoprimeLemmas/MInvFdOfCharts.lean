import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.KerInert.ScalM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.PairingIndexBounds.F

section lamC

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem qbar_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : s ^ n ∈ TaylorLogMetric.Qbar := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hs k
  | negSucc k =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hs _)

theorem lamC_of_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hs]

theorem lamC_mul_mem {s t : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (ht : t ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (s * t) = TaylorLogMetric.lamC lam s * TaylorLogMetric.lamC lam t := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.mul_mem hs ht), lamC_of_mem lam hs, lamC_of_mem lam ht, ← map_mul]
  rfl

theorem lamC_inv_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam s⁻¹ = (TaylorLogMetric.lamC lam s)⁻¹ := by
  rw [lamC_of_mem lam (TaylorLogMetric.Qbar.inv_mem hs), lamC_of_mem lam hs, ← map_inv₀]
  rfl

theorem lamC_zpow_mem {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (s ^ n) = (TaylorLogMetric.lamC lam s) ^ n := by
  rw [lamC_of_mem lam (qbar_zpow_mem hs n), lamC_of_mem lam hs, ← map_zpow₀]
  rfl

end lamC

section minv

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}


end minv

section scal

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : FData X D)
  (χ : TaylorLogMetric.IdE D → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

def MuAlg : Prop := ∀ j x, muT j x ∈ TaylorLogMetric.Qbar

def ChiAlg : Prop := ∀ 𝔞, χ 𝔞 ∈ TaylorLogMetric.Qbar

def ChiUnitG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j L0)))‖ = 1 ∧
      ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')))‖ = 1

def MuBdG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖(p : ℂ_[p]) ^ KG.expG X j L0 La' * TaylorLogMetric.lamC lam (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j L0))⁻¹)‖ ≤ 1

def BRG : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ‖TaylorLogMetric.lamC lam (KG.scalG fd χ muT j L0 La')‖ = ‖(p : ℂ_[p])‖ ^ (-KG.expG X j L0 La')

variable {X hfin fd χ muT lam}






end scal

end Formalism.L2.KerInert.ScalM

namespace Formalism.L2.KerInert.ScalM

open Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section inst

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)




end inst

end Formalism.L2.KerInert.ScalM
