module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorEmbedding
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

theorem _root_.GlobalTheory.T.cochain_product_alexander_whitney_formula : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  first | (exact @GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (exact GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (intros; apply GlobalTheory.PBFc.AWCross.isAW_pull_crossT  <;> assumption)
