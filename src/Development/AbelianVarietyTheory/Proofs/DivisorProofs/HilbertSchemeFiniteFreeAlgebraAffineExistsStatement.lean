module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExists
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.hilbertScheme_exists) | (exact GlobalTheory.HilbAff.hilbertScheme_exists) | (intros; apply GlobalTheory.HilbAff.hilbertScheme_exists <;> assumption)
