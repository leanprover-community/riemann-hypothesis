module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemNonzeroLocusOfIsActOf
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isProper_and_relAmple_lPow :
    ∀ (F : Type) [CommRing F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) [IsLocalRing F] (N : ℕ), 1 ≤ N → IsProper (fst (Over.mk t) P.A).left ∧ RelAmple (S := Spec (CommRingCat.of F)) (Over.mk (fst (Over.mk t) P.A).left) (LPow P.A P.L (N : ℤ) (Over.mk t)) := by
  intro F _ S P t _ N hN
  have hP := P.isAb.proper
  have H : IsPullback (snd (Over.mk t) P.A).left (fst (Over.mk t) P.A).left P.A.hom t :=
    (IsPullback.of_hasPullback t P.A.hom).flip
  have hp : IsProper (fst (Over.mk t) P.A).left := MorphismProperty.of_isPullback (P := @IsProper) H hP
  refine ⟨hp, ?_⟩
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hL := LB.isLB_pull P.isLB (snd (Over.mk t) P.A).left
  have hM : (LPow P.A P.L (N : ℤ) (Over.mk t)).IsLB := LB.isLB_linComb P.isLB _ _
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hL).1
    (AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample H)
  refine (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hM).2
    (((isAmpleLB_pow_iff hL hN).2 h₁).of_lbIso hM ?_)
  exact LBIso.chartPull (CoprimeTorsion.chartPullLPow P.A P.L (Over.mk t) N) (chartPullPowPull P.L _ N)
    (lbIso_refl (isLB_lbPow P.isLB N))

end GlobalTheory
