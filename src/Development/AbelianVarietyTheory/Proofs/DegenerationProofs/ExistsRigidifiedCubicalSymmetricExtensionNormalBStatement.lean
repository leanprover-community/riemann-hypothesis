module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (a : A.left ⟶ G.left), IsGrpPullback A G j a → ∀ (L : RigLB A) (c : CubicalStr A L) (M : LB G.left), M.IsLB → LBIso (M.pull a) L.L → ∃ (L' : RigLB G) (c' : CubicalStr G L') (m : CubeMap A G), m.F = a ∧ m.e = j ∧ m.IsPullCubical c c' ∧ (L.IsSymmetric → L'.IsSymmetric) := by
  first | exact @GlobalTheory.NormalCubeExt.exists_cubical_extension | exact GlobalTheory.NormalCubeExt.exists_cubical_extension | (intros; apply GlobalTheory.NormalCubeExt.exists_cubical_extension <;> assumption)
