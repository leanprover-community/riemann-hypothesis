module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactorsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isProjBy :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ L : LB A.left, L.IsLB → ∃ t : LB.Gen (Theta A L), t.IsGen := by
  intro k _ _ A _ hA hP L hL
  have := hA.comm
  have := hA.geomConnected
  have gi : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have conn : ConnectedSpace A.left := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have x : (Sp k : Scheme.{0}) := (default : PrimeSpectrum k)
    have h := A.hom.isConnected_preimage_singleton x
    have e : A.hom ⁻¹' {x} = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [e] at h
    exact connectedSpace_iff_univ.2 h
  have face : ∀ {Z : Over (Sp k)} (r : Z ⟶ G3 A) (i : Fin 3), r ≫ x3 A i = toUnit Z ≫ η[A] →
      Triv ((Theta A L).pull r.left) := fun {Z} r i h =>
    (CubeGen.triv_pull_iff L (thφ A (x3 A)) thε r.left).2
      (CubeGen.trivAt_of_formal hL _ (CubeGen.prod_face _ i (toUnit Z).left (congrArg (fun q => q.left) h)))
  exact GlobalTheory.T.theorem_of_cube_two_projective_factors k A A A η[A] η[A] η[A] hA.smooth hA.smooth hA.proper hA.proper hP hP gi gi conn
    (Theta A L) (DVR.linComb_isLB _ hL _ _) (face _ 0 (by simp [x3])) (face _ 1 (by simp [x3]))
    (face _ 2 (by simp [x3]))

end GlobalTheory
