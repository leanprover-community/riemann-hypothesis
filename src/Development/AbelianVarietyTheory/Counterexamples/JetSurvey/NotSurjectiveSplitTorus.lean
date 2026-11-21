import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnimodularSolTwoTorsion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlobFnsDvrChecks

theorem premises_met {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[3]) ℤ_[3] ∧ ∃ t : SAB H (Sp ℤ_[3]),
      IsProper ((Over.pullback (spMap (algebraMap ℤ_[3] (FractionRing ℤ_[3])))).obj t.G).hom ∧ ¬ IsIso t.G.hom := by
  open GlobalTheory.Models GlobalTheory.Models.EllipticModel GlobalTheory.WeierstrassCurve in
  obtain ⟨_, hc, -⟩ := GlobalTheory.exists_grpObj_weierstrass _ curve isUnit_curve_Δ
  open GlobalTheory.Models GlobalTheory.Models.EllipticModel GlobalTheory.WeierstrassCurve in
  have hA := isAbelianScheme_schemeOver _ curve isUnit_curve_Δ hc
  refine ⟨inferInstance, GlobalTheory.Models.tensorTriple H _ hA, ?_,
    GlobalTheory.Models.EllipticModel.not_isIso_tensorTriple H _ hA GlobalTheory.Models.EllipticModel.not_mono_toSpec⟩
  have := GlobalTheory.Models.isProper_tensorTriple (H := H) _ hA
  exact inferInstanceAs (IsProper (pullback.snd _ _))




end GlobalTheory.GlobFnsDvrChecks
