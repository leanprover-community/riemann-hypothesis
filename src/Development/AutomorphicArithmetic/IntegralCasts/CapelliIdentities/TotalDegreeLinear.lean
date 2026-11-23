module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.PV :
    Type → Type → Type → Type :=
    fun (ι A B : Type) ↦ MvPolynomial (ι × A ⊕ ι × B) ℂ

noncomputable def UpperTheory.Reformulated.B.TotalDegreeLinear.sub :
    {ι A B : Type} → [Fintype ι] → Matrix ι ι ℂ → Matrix ι ι ℂ → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B →ₐ[ℂ] UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B :=
    fun {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) ↦
      MvPolynomial.aeval
        (Sum.elim
          (fun (x : ι × A) ↦
            ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (g x.1 j) * MvPolynomial.X (Sum.inl (j, x.2)))
          fun (y : ι × B) ↦
          ∑ j : ι, (MvPolynomial.C : ℂ → MvPolynomial (ι × A ⊕ ι × B) ℂ) (h y.1 j) * MvPolynomial.X (Sum.inr (j, y.2)))

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le {σ τ : Type}
    (f : σ → MvPolynomial τ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private lemma UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le {ι τ : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → τ) :
    (∑ j : ι, (MvPolynomial.C (c j) : MvPolynomial τ ℂ) * MvPolynomial.X (v j)).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_X _).le

theorem UpperTheory.Reformulated.B.TotalDegreeLinear.main :
    ∀ {ι A B : Type} [inst : Fintype ι] (g h : Matrix ι ι ℂ) (p : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B),
      MvPolynomial.totalDegree ((UpperTheory.Reformulated.B.TotalDegreeLinear.sub g h : UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B → UpperTheory.Reformulated.B.TotalDegreeLinear.PV ι A B) p) ≤
        MvPolynomial.totalDegree p := by
  intro ι A B _ g h p
  refine UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_aeval_le _ ?_ p
  rintro (x | y)
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
  · exact UpperTheory.Reformulated.B.TotalDegreeLinear.totalDegree_linear_le _ _
