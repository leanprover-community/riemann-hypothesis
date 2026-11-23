module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ContinuousLocalCoefficientRepTwist
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCocycleTorsionOfHasPres
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem

@[expose] public section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
theorem _root_.GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (lam : ↥(OL C.LL)), Irreducible lam → GoodR D.nd i r → TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
    ∃ a : ℕ, (fun g => liftQ C.le k (z g)) ∈ divisibleCocycles (latC C (locOC C M)) ∧ ∀ g, lam ^ a • liftQ C.le k (z g) = 0 := by
  intro D i r w hw C lam hlam hGood _ k M z hz
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have htop : IsTopologicalRing ↥C.LL.1 := hG.2.2.2.1
  have hopen := hG.2.2.2.2
  have h1 := UpperTheory.KN.continuous_localCoefficientRep_twist D i r w hw C hGood
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C M z hz
  have h3 := @UpperTheory.KN.exists_cocycle_torsion_of_hasPres (Br.G D.nbr i w hw) ↥(OL C.LL) ↥C.LL.1 _ _ _ hdom hdvr _ _ htop _ hfr Subtype.val_injective lam _ _ _
    (fun x => locOC C (rTwO D.nd i r x)) (locOC C M) (fun g => liftQ C.le k (z g)) hlam hopen h1
  exact h3 h2
