module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingOfHomogeneousKerEq
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_complex_embedding_scaling_of_ker_eval_eq : ∀ (o K σ : Type) [CommRing o] [Field K] (β : o →+* K) (em : o →+* ℂ) (u : σ → K) (w : σ → ℂ) (a₀ : σ), u a₀ ≠ 0 → Subfield.closure (Set.range β ∪ Set.range (fun a => u a / u a₀)) = ⊤ → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) = RingHom.ker (MvPolynomial.eval₂Hom em w) → ∃ (e : K →+* ℂ) (c : ℂ), c ≠ 0 ∧ e.comp β = em ∧ ∀ a, e (u a) = c * w a := by
  first | exact @GlobalTheory.exists_embedding_of_homogeneous_ker_eq | exact GlobalTheory.exists_embedding_of_homogeneous_ker_eq | (intros; apply GlobalTheory.exists_embedding_of_homogeneous_ker_eq <;> assumption)
