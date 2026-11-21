import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MBLow.Cl

namespace GlobalTheory.MBLow.Cl

theorem exists_NF : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  intro g x hg
  subst hg
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, u, h₁, h₂, h₃, h₄, h₅, h₆⟩, -⟩ :=
    GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  exact ⟨u, τ, a, b, c, fun i => (2 * Real.pi * Complex.I : ℂ)⁻¹ • M i, h₁, h₂, hab.1, hab.2, hc, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MBLow.Cl
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalThetaNormalForm_keyDatum : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  atlas_forward_decl GlobalTheory.MBLow.Cl.exists_NF
