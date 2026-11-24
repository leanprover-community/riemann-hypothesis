module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
