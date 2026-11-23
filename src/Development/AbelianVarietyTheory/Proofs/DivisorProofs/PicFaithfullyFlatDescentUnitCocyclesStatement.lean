module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocycles
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

open TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles : ∀ (A : Type) [CommRing A], ∃ δ : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A, ∀ (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B], (∀ u v, UCoc A B u → UCoc A B v → δ B (u * v) = δ B u * δ B v) ∧ (∀ u, UCoc A B u → (δ B u = 1 ↔ ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w)) ∧ (∀ c : CommRing.Pic A, CommRing.Pic.mapAlgebra A B c = 1 → ∃ u, UCoc A B u ∧ δ B u = c) ∧ (∀ u, UCoc A B u → ∃ _ : Module.Invertible A (descMod A B u), CommRing.Pic.mk A (descMod A B u) = δ B u) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) (u' : (B' ⊗[A] B')ˣ), UCoc A B u → (u' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) → δ B' u' = δ B u := by
  first | (exact @GlobalTheory.pic_cech_descent) | (exact GlobalTheory.pic_cech_descent) | (intros; apply GlobalTheory.pic_cech_descent  <;> assumption)
