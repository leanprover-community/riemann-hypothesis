module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_isImmersion_isProjOver :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (W P : Scheme.{0}) (j : W ⟶ P) (p : P ⟶ Spec (CommRingCat.of R)),
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p → IsImmersion j → Alg (j ≫ p) I := by
  intro R _ _ I hI W P j p hp hj
  have hpb : IsProjBy p := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver p).2 hp
  have hprop : IsProper p := GlobalTheory.AbLaw.isProper_of_isProjBy R P p hpb
  have hA : Alg p I := GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective R I hI P p hpb
  have hjac : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hsep : IsSeparated p := inferInstance
  have hU : Alg (j.coborderRange.ι ≫ p) I :=
    GlobalTheory.T.formalClosedSubschemesAlgebraise_openImmersion R I hjac P _ p j.coborderRange.ι hsep inferInstance hA
  have hsepU : IsSeparated (j.coborderRange.ι ≫ p) := inferInstance
  have hW := GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion R I _ W (j.coborderRange.ι ≫ p) j.liftCoborder hsepU inferInstance hU
  rwa [← Category.assoc, Scheme.Hom.liftCoborder_ι] at hW

end GlobalTheory.FormalAlg
