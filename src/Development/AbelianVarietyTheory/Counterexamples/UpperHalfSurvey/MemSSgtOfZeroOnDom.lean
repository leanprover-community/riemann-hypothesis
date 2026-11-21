import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul

namespace GlobalTheory.FJCheck

open ReciprocityTheory.ChartRestriction.G.FD NumberField MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem fj_congr (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    {P Q : Frame X.Ψ r → ℂ} (h : ∀ x ∈ X.dom, P x = Q x) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have e : ∀ s : X.Ψ → ℝ, P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)
  unfold Data.fj
  simp only [e]


theorem chi_zero {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h0 : X.χ 0 γ ≠ 0 := fun e => by
    have := h γ hγ
    rw [e, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have := X.χ_add 0 0 γ hγ
  rw [add_zero] at this
  exact (mul_left_cancel₀ h0 (by rw [mul_one]; exact this)).symm





theorem zero_not_mem_dom (hr : 0 < r) : (0 : Frame X.Ψ r) ∉ X.dom := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  intro h
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  apply (h ⟨τ, hτ⟩).1
  have : mat (0 : Frame X.Ψ r) ⟨τ, hτ⟩ = 0 := rfl
  rw [this]; exact Matrix.det_zero

theorem mem_SSgt_of_zero_on_dom (la : Wt X.Ψ r) (c : ℝ) {P : Frame X.Ψ r → ℂ}
    (h : ∀ x ∈ X.dom, P x = 0) : P ∈ X.SSgt la c := by
  have hf : ∀ ξ, X.IsIso ξ → ∀ ν, ∀ x ∈ X.dom, X.fj la ξ ν P x = 0 := fun ξ hξ ν x hx => by
    rw [fj_congr X la hξ ν (Q := 0) h hx]; exact BoundedSectionAlgebra.fj_zero X la ξ x ν
  refine ⟨⟨⟨⟨(differentiableOn_const (0 : ℂ)).congr h, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩,
    0, fun x hx => ?_⟩, fun ξ hξ x hx => hf ξ hξ 0 x hx⟩, fun ξ hξ ν _ x hx => hf ξ hξ ν x hx⟩
  · rw [h _ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), h x hx, mul_zero]
  · rw [h _ (GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) hx), h x hx, mul_zero]
  · simp [Data.pnorm, h x hx]

open Classical in

theorem exists_ne_zero_mem_SSgt (hr : 0 < r) (la : Wt X.Ψ r) (c : ℝ) :
    ∃ P ∈ X.SSgt la c, P ≠ 0 ∧ ∀ x ∈ X.dom, P x = 0 := by
  have h : ∀ x ∈ X.dom, (fun y : Frame X.Ψ r => if y = 0 then (1 : ℂ) else 0) x = 0 := fun x hx => by
    have : x ≠ 0 := fun e => zero_not_mem_dom X hr (e ▸ hx)
    simp [this]
  exact ⟨_, mem_SSgt_of_zero_on_dom X la c h, fun e => by simpa using congrFun e 0, h⟩

end GlobalTheory.FJCheck
