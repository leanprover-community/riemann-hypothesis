module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TorsionExponentCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
