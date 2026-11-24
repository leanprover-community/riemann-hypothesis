module

public import Formalism.RealPlaceAnalysis.FockPairGl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.Proof.GenericSubmoduleMonomials

noncomputable def genSub (n n' k : ℕ) : MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ]
    MvPolynomial (Fin n × Fin k) (MvPolynomial (Fin n' × Fin n) ℂ) :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (X (v.1, t)) * X (t, v.2))

theorem map_eval_genSub (n n' k : ℕ) (x : Matrix (Fin n') (Fin n) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) :
    map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k f) =
      aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [genSub, aeval_C, aeval_C]
    simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hv : map (eval (fun v : Fin n' × Fin n => x v.1 v.2)) (genSub n n' k (X v)) =
        ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ) := by

      rw [genSub, aeval_X, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_C, map_X, eval_X]
    rw [map_mul, map_mul, hp, map_mul, hv, aeval_X]

theorem repr_basisMonomials {σ : Type} (φ : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (basisMonomials σ ℂ).repr φ m = AddMonoidAlgebra.coeff φ m := rfl

theorem exists_pairing : ∀ (n n' k : ℕ), ∃ T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ, ∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f)) := by
  intro n n' k
  refine ⟨(basisMonomials (Fin n × Fin k) ℂ).constr ℂ (fun m => ((∏ j ∈ m.support, (m j).factorial : ℕ) : ℂ) •
    (((lcoeff (MvPolynomial (Fin n' × Fin n) ℂ) m).restrictScalars ℂ) ∘ₗ (genSub n n' k).toLinearMap)), ?_⟩
  intro φ f x
  have hs : ((basisMonomials (Fin n × Fin k) ℂ).repr φ).support = φ.support := by
    ext m
    rw [Finsupp.mem_support_iff, repr_basisMonomials, mem_support_iff]

  rw [Module.Basis.constr_apply, Finsupp.sum, hs, fockF, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [repr_basisMonomials, ← map_eval_genSub, coeff_map, coeff_map]
  simp only [LinearMap.smul_apply, smul_eval, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.restrictScalars_apply, lcoeff_apply, starRingEnd_apply, star_star]
  ring

end GlobalTheory.Proof.GenericSubmoduleMonomials
