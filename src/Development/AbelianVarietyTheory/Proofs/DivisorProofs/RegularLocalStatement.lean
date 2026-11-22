module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.DetHT

namespace GlobalTheory.DetHT.RegLoc

theorem mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (c : Γ(X, U)) :
    x ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  rwa [hU.fromSpec_primeIdealOf] at h₂

end GlobalTheory.DetHT.RegLoc
