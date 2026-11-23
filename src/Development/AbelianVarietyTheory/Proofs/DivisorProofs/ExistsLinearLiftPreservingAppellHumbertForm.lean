module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGramLift

theorem exists_lift : ∀ (Q P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (u' : HolUnif P.A P.L g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (f : Q.A ⟶ P.A), IsMonHom f → LBIso (lbPow (P.L.pull f.left) 1) (lbPow Q.L 1) → ∀ (n : ℕ) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (Wc : Fin n → Fin Q.g → ℂ), (∀ i, IsTangent (v' i) ∧ u.IsDiff (Wc i) (v' i)) → ∀ (m : ℕ) (a : Fin m → Fin n → ℂ) (tv : Fin m → (epsR ℂ ⟶ P.A)) (Xv : Fin m → Fin g → ℂ), (∀ i, u'.IsDiff (Xv i) (tv i)) → (∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (a i) v' q → q ≫ f = tv i) → ∃ L : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x x', hermForm Hm' (L x) (L x') = hermForm Hm x x') ∧ ∀ i, L (∑ k, a i k • Wc k) = Xv i := by
  intro Q P g u Hm χ u' Hm' χ' hu hu' f hf hL n v' Wc hv m a tv Xv htv hq
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all P g u' Hm' χ' hu'
  obtain ⟨F, hF, -, hFd, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A P.A Q.isAb P.isAb Q.L P.L Q.g g u u'
    h1 h2 f hf
  refine ⟨F, fun x x' => ?_, fun i => ?_⟩
  · have := GlobalTheory.hermForm_pull_eq_of_lbIso_pow Q.A P.A Q.L P.L Q.isLB P.isLB Q.g g u u' Hm χ Hm' χ' hu hu' f F hF 1 1 hL x x'
    simpa using this
  · have hc : IsLieComb (a i) v' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (a i) v') :=
      (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff (a i) v' _).2 rfl
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g n u Wc v' (a i) _
      (fun k => (hv k).1) (fun k => (hv k).2) hc
    have ht := GlobalTheory.HermHom.isTangent_of_isLieComb u (fun k => (hv k).1) (fun k => (hv k).2) hc
    obtain ⟨ht', hd'⟩ := hFd _ _ ht hd
    rw [hq i _ hc] at ht' hd'
    obtain ⟨w, -, hw⟩ := h1 (tv i) ht'
    exact (hw _ hd').trans (hw _ (htv i)).symm

end GlobalTheory.LieGramLift
