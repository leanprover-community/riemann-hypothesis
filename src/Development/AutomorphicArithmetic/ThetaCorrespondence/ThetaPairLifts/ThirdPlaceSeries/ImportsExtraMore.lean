module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltTer
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
noncomputable section
namespace GlobalTheory.AdmGTwoLarge
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  intro hF D L nch i r π ρ hf hP _ hg _ hr hπ hρ
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (hf.admJ L hP)
  have hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := by
    obtain ⟨-, e, he⟩ := hρ
    exact ⟨e, fun g u => he g u⟩
  exact _root_.GlobalTheory.GTwoTheta.main_alt_alt hF D L hf.g2.1 hJ.1 hJ.2.2.1 i r (fun _ => ρ) π hr (hg 0) (hg 1) hπ hD
end GlobalTheory.AdmGTwoLarge
end
end
