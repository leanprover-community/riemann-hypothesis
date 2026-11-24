module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineLeOrDisjoint
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FormalAlg

theorem exists_isProper_isImmersion_isProjOver : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first
  | exact @_root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow
  | (apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseClosedAffineSubsets.chow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseClosedAffineSubsets.chow ..)

end GlobalTheory.FormalAlg
