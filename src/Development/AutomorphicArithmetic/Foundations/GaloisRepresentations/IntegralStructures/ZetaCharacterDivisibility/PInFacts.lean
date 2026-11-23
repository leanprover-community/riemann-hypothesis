module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem pow_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (n : ℕ) :
    P ^ n * A = A * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, pow_succ]

private theorem aeval_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (Q : k[X]) :
    aeval P Q * A = A * aeval R Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, one_mul, Matrix.smul_mul, Matrix.mul_smul, pow_intertwine h n]

private theorem left_cancel {k : Type} [Field k] {a d : ℕ} {A : Matrix (Fin d) (Fin a) k} (hA : A.rank = a)
    {M N : Matrix (Fin a) (Fin a) k} (h : A * M = A * N) : M = N := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := by
      rw [Matrix.finrank_range_mulVecLin]; exact hA
    rw [h2, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hinj := LinearMap.ker_eq_bot.mp hker
  ext i j
  have hv : M.mulVec (Pi.single j 1) = N.mulVec (Pi.single j 1) := by
    apply hinj
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]
  simpa using congrFun hv i

theorem UpperTheory.Gal.Int.Div.inFacts_of :
    InFacts := by
  intro Γ k _ _ a d r ρ ⟨A, hA, hc⟩
  refine ⟨hA ▸ A.rank_le_height, fun g hg => ?_, fun g Q hQ => ?_⟩
  · have h := hc g
    rw [hg] at h
    apply Units.ext
    apply left_cancel hA
    simpa using h.symm
  · apply left_cancel hA
    rw [← aeval_intertwine (hc g) Q, hQ]
    simp
