module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfMumfordBundleLiftSqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZeroStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SqStep.exists_lift : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hsq Y₀ _ hY₀ L₀ hL₀ hamp hK
  obtain ⟨Y, _, i, l, Q, hY, hpb, hsqr, hQ, a₁, a₂, hQi⟩ :=
    GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle R R₀ π hπ hsq Y₀ hY₀ L₀ hL₀ hamp hK
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero R R₀ π hπ hsq Y₀ Y i l hY₀ hY hpb hsqr L₀ Q hL₀ hQ a₁ a₂ hQi
  haveI : Smooth Y.hom := hY.smooth
  have hamp' : RelAmple Y L :=
    GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ hsq Y Y₀ i hpb.1 inferInstance L L₀ hL hL₀ hLi hamp
  exact ⟨Y, inferInstance, L, i, hY, hL, hamp',
    GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero R R₀ π hπ hsq Y₀ Y i hY hpb L₀ L hL₀ hL hamp' hLi hK, hpb, hLi⟩
