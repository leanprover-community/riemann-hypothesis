module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RankPosNegativeWeightBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroCuspForm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatDegreeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatValStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadingStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

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

noncomputable section
namespace GlobalTheory.CovTop.LowPos
open GlobalTheory.FlatTw GlobalTheory.FlatLine
theorem lowered_rank_pos_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hP hG hQ hS hKS hLie
  have R := _root_.GlobalTheory.T.weight_conditions_at_index'
  have F := _root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le (_root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints hP)
  have S := _root_.GlobalTheory.T.exists_ne_zero_cuspOn_of_covers hP hG hQ hS hKS.toroidalChartsForFan hLie
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (R.and (F.and S)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, -, -, hs⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  obtain ⟨Z, g, hg, hg0⟩ := hC i hi Y hY
  have hgood := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
    (hs _ (Or.inl rfl)).1 (hs _ (Or.inl rfl)).2
  obtain ⟨g', hg', hg'0⟩ := _root_.GlobalTheory.CovTop.LowPos.exists_twist_ne_zero_of_lowered hP p.T _ Y _ _ hL hj hY.1 hFl (uM p i)
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)) ((p.κ i).n / 2) Z hg hg0
  exact rk_pos hgood (mem_cuspW_of_exZ hY.1.unf (exZ_lowered _ _ _ _ _ hn) hg'.1) hg'0
end GlobalTheory.CovTop.LowPos
end
end
section

theorem _root_.GlobalTheory.T.rank_pos_negative_weight_bundle_on_covers : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt | exact _root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.LowPos.lowered_rank_pos_alt_alt <;> assumption)
end
end
