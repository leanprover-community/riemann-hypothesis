module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidLineBundleIsoDescentAlongGaloisCover
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  first | exact @GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | exact GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover | (intros; apply GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover <;> assumption)
