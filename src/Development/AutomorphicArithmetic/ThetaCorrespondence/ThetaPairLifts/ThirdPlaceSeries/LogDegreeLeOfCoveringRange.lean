module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BinomialFlagDimensionDegreeBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogTopDimensionBoundCovering
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
theorem log_degree_le_of_covering_range_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  intro hX hP hG hQ hSg hFan hSA hDG hSz hFD
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.binomial_flag_dimension_degree_bound_alt_alt hX hP hG hQ hSg hFan hSA hDG hSz hFD) (_root_.GlobalTheory.T.log_finrank_cuspOn_le hP hSz)) hSz) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max x1 x2) x3, ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hA := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hB := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hz := h3 x hx ((le_max_right _ _).trans hle) ι p hp i
  set PP := (Fm.parT x hx ι).PP with hPP
  obtain ⟨⟨u1, hu1⟩, hqq⟩ := hz.2.2.2.2.2.2 hi
  have hT := (hqq _ hu1).1
  have hbin : 1 ≤ (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) := Nat.choose_pos (by omega)
  have hle' : GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) :=
    (Nat.le_mul_of_pos_left _ hbin).trans hA
  have hdg0 : (0 : ℝ) ≤ Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z := Nat.cast_nonneg _
  rcases hdg0.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact (Real.log_natCast_nonneg _).trans hB
  · have h1 : Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z ≤ (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) := by
      exact_mod_cast hle'
    exact (Real.log_le_log h0 h1).trans hB
end GlobalTheory.CovTop.DgLog
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | exact _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | (intros; apply _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt <;> assumption)
end
end
