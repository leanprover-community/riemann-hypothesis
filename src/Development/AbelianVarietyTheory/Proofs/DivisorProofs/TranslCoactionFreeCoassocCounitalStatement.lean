module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
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

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.transl_coaction_free_coassoc_counital : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by
  first | exact @GlobalTheory.PDivGroup.transl_free | exact GlobalTheory.PDivGroup.transl_free | (intros; apply GlobalTheory.PDivGroup.transl_free <;> assumption)
