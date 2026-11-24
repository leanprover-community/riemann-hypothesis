module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundles
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_model_vector_bundles : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagBundle | exact GlobalTheory.CompanionTheory.Ar.exists_flagBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagBundle <;> assumption)
