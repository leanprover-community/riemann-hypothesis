module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_lattice_vector_bundle_of_smooth : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → M.lat.IsVB g ⊤ ∧ M.omLat.IsVB g ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieLat_isVB | exact GlobalTheory.CompanionTheory.Ar.lieLat_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.lieLat_isVB <;> assumption)
