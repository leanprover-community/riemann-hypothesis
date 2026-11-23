module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.TheoremFiveAtS
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v := by
  intro D L nch i r π ρ hF _ _ hHG hr _ _ v hv
  have hIne : TruncatedSeriesCountingIdentities.admG5 i r := galois_condition_five_of D i r hF.Conclusion2.1 hHG hr
  have hTame : TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := (GlobalTheory.TameDesign.main D i).2
  have hS := ((D.nd.S_def i v).1 hv).1
  have hvI := hIne v (Or.inl hv)
  have hvT := hTame v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hvI.2 hk hv hvT.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hvI.1 (Or.inr hp)) x).1 γ hγ, hvT.2.2.2 hv hp⟩
end GlobalTheory.TheoremFiveAtS
end
