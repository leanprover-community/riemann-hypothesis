import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
end

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  atlas_forward_decl GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho
