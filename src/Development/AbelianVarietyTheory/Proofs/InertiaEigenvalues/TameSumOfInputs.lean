import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDense

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_fixed_away : ∀ D : D7, WildOne D → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  first | exact @GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | exact GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | (intros; apply GlobalTheory.TypeLeaf.tameFixed_of_cuspidal <;> assumption)
end

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_of_frobenius_dense : ∀ D : D7, WildOne D → (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ (v : D.nd.PlG k) (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k w := by
  first | exact @GlobalTheory.TypeLeaf.ConjPlace.tameAnyAt_of_isConjPl | exact GlobalTheory.TypeLeaf.ConjPlace.tameAnyAt_of_isConjPl | (intros; apply GlobalTheory.TypeLeaf.ConjPlace.tameAnyAt_of_isConjPl <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem tameSum_of_inputs : ∀ D : D7, WildOne D →
    (∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k →
      ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1) →
    GalAway D → FrobDense D → PointPar D → TameSum D := by
  intro D hW hχ hG hF hP i Sig hx hfull hc ρ hρ k hk
  obtain ⟨x, hx⟩ := hx
  obtain ⟨π, rfl⟩ := hc
  obtain ⟨h1, h2⟩ := hP i x π hx
  refine ⟨GlobalTheory.T.tame_fixed_away D hW hG hF i π ρ h1 h2 hfull hρ k hk, fun w hw ht => ?_⟩
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · subst hv
    exact GlobalTheory.T.tame_any_at_place D hG hF i π ρ h1 h2 hfull hρ k hk v
  · exact GlobalTheory.T.tame_of_frobenius_dense D hW hχ hG hF i π ρ h1 h2 hfull hρ k hk v w hv ht

end GlobalTheory.TypeLeaf
end
end
