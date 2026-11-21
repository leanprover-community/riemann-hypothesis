import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockDeltaBasePolynomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockActionBasePolynomial

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

include hΨ in
theorem exists_tau : Nonempty D.what₂.Tau := by
  let τ₀ : D.host.E →+* ℂ := (IsAlgClosed.lift : D.host.E →ₐ[ℚ] ℂ).toRingHom
  by_cases h : InPsi H τ₀
  · obtain ⟨ρ, -⟩ := (hΨ τ₀).1 h
    exact ⟨ρ⟩
  · obtain ⟨ρ, -⟩ := (hΨ (conjEmb τ₀)).1 ((GlobalTheory.Harm.not_mem_hostType_iff H τ₀).1 h)
    exact ⟨ρ⟩

include hΨ in
theorem le_of_good {w : Weight D n} {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hw : w.Good) (hwt : WtIs Dw w a) :
    Dw.p + Dw.q ≤ n := by
  obtain ⟨ρ⟩ := exists_tau hΨ
  have := hw.le ρ
  rw [(hwt ρ).1, (hwt ρ).2.1] at this
  exact this

include hΨ in
theorem antitone_of_good {w : Weight D n} {a : (D.host.E →+* ℂ) × ℕ → ℕ} (hw : w.Good) (hwt : WtIs Dw w a) :
    (∀ t : {τ : D.host.E →+* ℂ // InPsi H τ}, Antitone fun i : Fin Dw.p => a (t.1, i)) ∧
      ∀ t : {τ : D.host.E →+* ℂ // InPsi H τ}, Antitone fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) := by
  have hn := le_of_good Dw hΨ hw hwt
  constructor
  · rintro ⟨τ, hτ⟩ i j hij
    obtain ⟨ρ, rfl⟩ := (hΨ τ).1 hτ
    obtain ⟨hp, hq, hap, -⟩ := hwt ρ
    dsimp only
    rw [hap i i.2, hap j j.2]
    have h1 := (w.lam ρ).anti (show (⟨i, by omega⟩ : Fin n) ≤ ⟨j, by omega⟩ from hij)
    rw [hw.lam_eq, hw.lam_eq, if_pos (by rw [hp]; exact j.2), if_pos (by rw [hp]; exact i.2)] at h1
    exact_mod_cast (add_le_add_iff_right _).1 h1
  · rintro ⟨τ, hτ⟩ i j hij
    obtain ⟨ρ, rfl⟩ := (hΨ τ).1 hτ
    obtain ⟨hp, hq, -, ham⟩ := hwt ρ
    dsimp only
    rw [show ComplexEmbedding.conjugate (tauE D ρ) = conjEmb (tauE D ρ) from rfl, ham i i.2, ham j j.2]
    have hij' : (j : ℕ) ≥ i := hij
    have h1 := (w.lam ρ).anti (show (⟨n - 1 - j, by omega⟩ : Fin n) ≤ ⟨n - 1 - i, by omega⟩ from
      show n - 1 - (j : ℕ) ≤ n - 1 - i by omega)
    rw [hw.lam_eq, hw.lam_eq] at h1
    simp only [hp, hq] at h1
    have e1 : n - 1 - (n - 1 - (i : ℕ)) = i := by omega
    have e2 : n - 1 - (n - 1 - (j : ℕ)) = j := by omega
    have c1 : ¬ (n - 1 - (i : ℕ) < Dw.p) := by omega
    have c2 : ¬ (n - 1 - (j : ℕ) < Dw.p) := by omega
    have c3 : n - Dw.q ≤ n - 1 - (i : ℕ) := by omega
    have c4 : n - Dw.q ≤ n - 1 - (j : ℕ) := by omega
    simp only [c1, c2, c3, c4, e1, e2, if_true, if_false] at h1
    have : (w.am ρ j : ℤ) ≤ w.am ρ i := by linarith
    exact_mod_cast this

end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

theorem isLetters_letterEquiv : IsLetters Dw (letterEquiv (n := n) Dw hΨ hm) := by
  rintro ⟨τ, i, b⟩
  rcases GlobalTheory.Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate _)
    (GlobalTheory.Harm.not_mem_hostType_iff H) τ with h | ⟨τ', h, rfl⟩
  · have e : letterEquiv Dw hΨ hm ⟨τ, i, b⟩ = ((tauPsi hΨ).symm ⟨τ, h⟩,
        Fin.cast hm.symm (Fin.castAdd Dw.q (i.cast (GlobalTheory.Harm.mult_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_of_mem Dw h]
      rfl
    rw [e]
    exact ⟨rfl, Or.inl ⟨(congrArg Subtype.val ((tauPsi hΨ).apply_symm_apply ⟨τ, h⟩)).symm, rfl⟩⟩
  · have e : letterEquiv Dw hΨ hm ⟨ComplexEmbedding.conjugate τ', i, b⟩ = ((tauPsi hΨ).symm ⟨τ', h⟩,
        Fin.cast hm.symm (Fin.natAdd Dw.p (i.cast (GlobalTheory.Harm.mult_conjEmb_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_conjugate Dw h]
      rfl
    rw [e]
    refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
    change conjEmb τ' = conjEmb (tauE D ((tauPsi hΨ).symm ⟨τ', h⟩))
    rw [← tauPsi_apply hΨ, Equiv.apply_symm_apply]


end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters


end GlobalTheory.FockLetters
