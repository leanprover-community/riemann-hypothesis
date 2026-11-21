import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)

omit [NumberField E] [IsCMField E] in
theorem ln_std (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _

theorem std_one (n : ℕ) (β : c.F) (hβ : β = 1 ∨ β = -1) :
    β ≠ 0 ∧ BetaIs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β ∧ BetaAbs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β := by
  have h1 : Submodule.span (𝓞 c.F) {β} = 1 := by
    rcases hβ with rfl | rfl
    · exact (Submodule.one_eq_span).symm
    · rw [Submodule.one_eq_span, ← Set.neg_singleton, Submodule.span_neg]
  refine ⟨by rcases hβ with rfl | rfl <;> simp, ?_, ?_⟩
  · unfold BetaIs
    rw [h1, one_mul, ln_std]
  · intro σ
    rw [ln_std]
    rcases hβ with rfl | rfl <;> simp

theorem betaH_congr {n m : ℕ} (Λ : GenLat E n) (Λ' : GenLat E m)
    (h : ∀ β : c.F, (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) ↔
      (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ' β ∧ BetaAbs (Dw := Dw) c Λ' β)) :
    betaH (Dw := Dw) c Λ = betaH (Dw := Dw) c Λ' := by
  unfold betaH
  have e := funext fun β => propext (h β)
  generalize (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) = p at e ⊢
  subst e
  rfl

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

omit [NumberField E] [IsCMField E] in

theorem detSet_scale {n : ℕ} (M M' : Submodule (𝓞 E) (Fin n → E)) (a : E)
    (h : ∀ v, v ∈ M' ↔ ∃ w ∈ M, v = a • w) : detSet M' = (fun d => a ^ n * d) '' detSet M := by
  have key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) =
      a ^ n * Matrix.det (Matrix.of fun i j => w j i) := by
    intro w
    have : (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i) := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin]
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hw' using fun i => (h (v i)).1 (hv i)
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    have : v = fun j => a • w j := funext hw'
    subst this
    exact (key w).symm
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩




end GlobalTheory.BetaCounterexample
