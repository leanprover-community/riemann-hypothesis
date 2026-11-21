import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsFurther
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem

section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_bundle_smooth : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → Geo.IsSmoothHerm A := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | exact GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.smooth_of_isHermRep <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_codimension_one : GlobalTheory.CompanionTheory.MixZ.CodimOne := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.codimOne_holds | exact GlobalTheory.CompanionTheory.MixZ.codimOne_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.codimOne_holds <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_curve_intersection_formula : GlobalTheory.CompanionTheory.MixZ.CurveInt := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.curveInt | exact GlobalTheory.CompanionTheory.MixZ.curveInt | (intros; apply GlobalTheory.CompanionTheory.MixZ.curveInt <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_of_full_intersection_system : GlobalTheory.CompanionTheory.MixZ.PtDict → GlobalTheory.CompanionTheory.MixZ.CodimOne → GlobalTheory.CompanionTheory.MixZ.ExistsRat → GlobalTheory.CompanionTheory.MixZ.CycleOfRat → GlobalTheory.CompanionTheory.MixZ.ArchIntEq → GlobalTheory.CompanionTheory.MixZ.VertEq → GlobalTheory.CompanionTheory.MixZ.PtLen → GlobalTheory.CompanionTheory.MixZ.CurveInt → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement → ∀ II : ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem, ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → GlobalTheory.CompanionTheory.MixZ.HeightEq II := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.heightEq_holds | exact GlobalTheory.CompanionTheory.MixZ.heightEq_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.heightEq_holds <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem isArithVar_mpStr (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem dim_of_isArithVar (hD : GlobalTheory.CompanionTheory.MixZ.PtDict) {m : ℕ} {n : Fin (m + 1) → ℕ} {Z : Scheme.{0}} [IsIntegral Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {d : ℕ} (hd : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) d) :
    topologicalKrullDim Z = d := by
  obtain ⟨d', hd'⟩ := (isArithVar_mpStr m n).exists_dim_eq i
  obtain ⟨-, -, h₃, -⟩ := hD m n Z i d' hd'
  have h₄ := h₃ hd.2.2.1
  have e : d' + Fintype.card (Fin (m + 1)) = d + Fintype.card (Fin (m + 1)) := by
    exact_mod_cast h₄.2.2.2.symm.trans hd.2.2.2
  rw [hd', Nat.add_right_cancel e]

end GlobalTheory.CompanionTheory.MPDict
end
end
