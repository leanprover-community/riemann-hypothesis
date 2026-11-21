import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import BuildAid.ForwardExisting

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem constantCoeff_DpolyN_jEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  intro k _ d n F Ix _ cp u P m f g hP hfg
  classical
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P f _ subset_rfl,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P g _ subset_rfl]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  refine GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr F cp u e f g fun mo hmo => ?_
  refine hfg mo (hmo.trans (le_trans ?_ hP))
  have := MvPolynomial.le_totalDegree he
  rwa [Finsupp.degree_apply]

end GlobalTheory.ChartCmp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  atlas_forward_decl GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq
