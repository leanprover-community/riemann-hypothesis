module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoefficientExtensionDecomposition
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory
theorem pointInputAwayFromTypePrimes_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.PtCore.PtFam D X.r X.ρ → _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π := by
  intro hF D X hX hG i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  exact ⟨hX.good i, fun x => (hX.good i x).1, hZ, hd, hX.cont i π, fun w hw C x =>
    ((_root_.GlobalTheory.T.semisimple_decomposition_of_good_galois_local hF D i _ _ π (hX.good i) (hG i _ (hX.good i)) h0 h1 hd w hw C).2 x).2⟩
end GlobalTheory
end
