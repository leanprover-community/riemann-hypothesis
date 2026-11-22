module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

variable {X Y : Scheme.{0}}

def evU {Z : Scheme.{0}} (g : Z ⟶ X) {W : X.Opens} (hg : ∀ z, g z ∈ W) (f : Γ(X, W)ˣ) : Γ(Z, ⊤)ˣ :=
  res (fun z _ => hg z : (⊤ : Z.Opens) ≤ g ⁻¹ᵁ W) (pullU g W f)

section Eigen

variable {K : Type} [Field K] {A A' T : Over (Sp K)} [GrpObj A] [GrpObj A']

end Eigen

end GlobalTheory.EigenDescent
