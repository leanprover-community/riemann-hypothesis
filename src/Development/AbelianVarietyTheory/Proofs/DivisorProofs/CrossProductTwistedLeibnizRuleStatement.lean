module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRule
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.crossProductTwisted_leibniz_rule : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ} (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k') (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m), δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  first | (exact @GlobalTheory.PBFc.crossT_leibniz) | (exact GlobalTheory.PBFc.crossT_leibniz) | (intros; apply GlobalTheory.PBFc.crossT_leibniz  <;> assumption)
