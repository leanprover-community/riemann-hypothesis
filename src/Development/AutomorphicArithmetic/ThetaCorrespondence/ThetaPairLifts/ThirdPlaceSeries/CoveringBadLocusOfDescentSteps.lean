module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadComponentsIndefinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLiftAtDefiniteBadPlaces
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
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
namespace GlobalTheory.CovTop
theorem covering_bad_locus_of_descent_steps_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal →
    _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition →
    _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  intro hX hP hGD hQ hST hTF hSA hGC hGr hEx hDG hS hF hD hSh
  have h1 := _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal hP hGC hGr
  have h2 := _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree hX hP hGD hQ hST hTF hSA hGC hGr hDG hS hF hD hSh
  unfold _root_.GlobalTheory.CovTop.LiftBadSet _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at h2
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1
  unfold _root_.GlobalTheory.CovTop.DeepExistence _root_.GlobalTheory.CovTop.LiftsCondition at hEx
  refine ((h1.and h2).and hEx).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, e⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := e x hx hle ι p hp
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (Fm.D x ι).R.m with hlt | hge
  · obtain ⟨Y, hY⟩ := a3 i hlt
    exact a2 i hlt Y hY
  · exact a1 i (le_antisymm (Nat.succ_le_of_lt i.isLt) hge)
end GlobalTheory.CovTop
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

theorem _root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.LiftBadSet := by
  first | exact @_root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | exact _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_bad_locus_of_descent_steps_alt <;> assumption)
end
end
