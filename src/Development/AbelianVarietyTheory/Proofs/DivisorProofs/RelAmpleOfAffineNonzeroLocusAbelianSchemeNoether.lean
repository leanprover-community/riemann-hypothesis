module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTranslatesCoverGeometricFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AffineLocusAmple

theorem relAmple_of_affine_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  intro R _ _ A _ hA M hM s hV hs
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K _ _ y => ?_
  obtain ⟨n, a, ha⟩ := GlobalTheory.T.exists_finite_translates_cover_geometric_fibre (Sp R) A hA _ K y fun z => hs (y z)
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Sp K))
  have h := GlobalTheory.T.isAmple_lineBundle_pullback_of_translates R A hA M hM _ _ rfl hV ⟨M, hM, s, rfl, rfl⟩ (Over.mk y) n a ha
    fun i => GlobalTheory.cechPic_sp_field_eq_zero K _
  exact h

end GlobalTheory.AffineLocusAmple
