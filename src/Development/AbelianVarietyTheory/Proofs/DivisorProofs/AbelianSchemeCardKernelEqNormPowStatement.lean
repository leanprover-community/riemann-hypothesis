module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPow
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct


theorem _root_.GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  first | (exact @GlobalTheory.AVCount.card_ker_eq_norm_pow) | (exact GlobalTheory.AVCount.card_ker_eq_norm_pow) | (intros; apply GlobalTheory.AVCount.card_ker_eq_norm_pow  <;> assumption)
