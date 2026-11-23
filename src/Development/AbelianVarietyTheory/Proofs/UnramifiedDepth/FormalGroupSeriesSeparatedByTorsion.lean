module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPowStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemSupSpanXPowIffAndIsAdicComplete
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem mem_span_of_killed {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (N : ℕ)
    (h : ∀ q : QF F N, (∀ φ : QF F N →ₐ[R] R, φ q = 0) → q = 0) (f : PS R 1 d)
    (hf : ∀ φ, Killed F N φ → φ f = 0) : f ∈ Ideal.span (Set.range (mulF F N)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine h _ fun φ => ?_
  refine hf (φ.comp (Ideal.Quotient.mkₐ R _)) fun j => ?_
  have : Ideal.Quotient.mk (Ideal.span (Set.range (mulF F N))) (mulF F N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [this]

theorem mem_span_mulF_of_killed_and_eq_zero_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hc d F hFH
  have h1 : ∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) →
      f ∈ Ideal.span (Set.range (mulF F.F (p ^ k))) :=
    fun k f hf => mem_span_of_killed F.F (p ^ k) (hFH k).2.2 f hf
  refine ⟨h1, fun f hf => ?_⟩
  have hH := ((mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2
    hc).toIsHausdorff
  refine hH.haus f fun k => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  refine (Ideal.span_le.2 ?_) (h1 k f fun φ hφ => hf φ ⟨k, hφ⟩)
  rintro _ ⟨j, rfl⟩
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p k j

end GlobalTheory.ChF
