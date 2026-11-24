module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfinitePowCharEqOneOfAdditiveFamily
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.infinite_pth_roots_of_additive_family : ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k) (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) → Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 → em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  first | exact @GlobalTheory.infinite_pow_char_eq_one_of_additive_family | exact GlobalTheory.infinite_pow_char_eq_one_of_additive_family | (intros; apply GlobalTheory.infinite_pow_char_eq_one_of_additive_family <;> assumption)
