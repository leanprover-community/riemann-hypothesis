module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_cocycle_coboundary_iff : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  first | (exact @GlobalTheory.CechOne.cech1) | (exact GlobalTheory.CechOne.cech1) | (intros; apply GlobalTheory.CechOne.cech1  <;> assumption)
