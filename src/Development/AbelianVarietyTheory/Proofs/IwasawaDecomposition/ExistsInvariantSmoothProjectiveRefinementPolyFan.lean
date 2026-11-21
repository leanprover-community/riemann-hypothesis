import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSimplicialLabelledFanRefinement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_simplicial_labelled_fan_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ lab : InvFun (𝓞 E), IsPolyFan H.bar q φ ∧ IsTwInv H φ ∧ IsTwInv H lab ∧ SimpLab H.bar q φ lab ∧ Subordinate H.bar q φ ψ := by
  first | exact @GlobalTheory.PolFan.exists_simpLab_refinement | exact GlobalTheory.PolFan.exists_simpLab_refinement | (intros; apply GlobalTheory.PolFan.exists_simpLab_refinement <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_smooth_refinement_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  first | exact @GlobalTheory.PolFan.resolution | exact GlobalTheory.PolFan.resolution | (intros; apply GlobalTheory.PolFan.resolution <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.exists_smooth_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ' γ → ψ.LinearOn γ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := GlobalTheory.T.exists_invariant_simplicial_labelled_fan_refinement E H q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := GlobalTheory.T.exists_invariant_smooth_refinement_polyFan E H q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩
end
