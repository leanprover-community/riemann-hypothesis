module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTerStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.HubGood
theorem ambAll_goodPoints_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambBlock (D := D) i (X.r i) (X.ρ i) π := by
  intro hF D L X hG hJa hJc hX i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg2 := _root_.GlobalTheory.T.semisimpleDecomposition_of_goodR hF D L hG hJa hJc i (X.r i) (X.ρ i) π (hX.good i) h0 h1 hZ hd
  have hWT := GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp D i (X.r i) (X.ρ i) π (X.dc i) hg2 hd
  exact ⟨hWT.2, hWT.1, GlobalTheory.T.ambientFiltration_every_declaration D i (X.r i) (X.ρ i) π (X.dc i), GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i (X.r i) (X.ρ i) π hd⟩
end GlobalTheory.HubGood
end
