import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
import BuildAid.ForwardExisting

section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.rho_hom
