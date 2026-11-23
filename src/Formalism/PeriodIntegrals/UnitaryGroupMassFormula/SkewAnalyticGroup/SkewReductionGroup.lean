module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.ExpMulVecFix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkewAnalyticGroup.Development
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open Matrix Filter Topology

noncomputable section

namespace QnRdSkewW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  apply QnYLeibnizW.exp_mul_fix <;> assumption

end Linfty

lemma exp_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (hXv : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  apply QnYLeibnizW.exp_mulVec_fix <;> assumption

lemma exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by
  apply QnYLeibnizW.exp_mem_UH <;> assumption

lemma glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  apply QnYLeibnizW.glev_mul <;> assumption

lemma glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ⋂ a : Fin r, ⋂ (_ : a.val < i.val),
        ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by
    ext g
    simp only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

lemma exp_mem_glev {k r : ℕ} {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  obtain ⟨hL, hF⟩ := hX
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  refine ⟨exp_mem_UH _ _ hH ?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]
  · obtain ⟨h1, h2⟩ := hF a ha
    exact ⟨exp_mulVec_fix X _ h1 t, exp_mulVec_fix X _ h2 t⟩

theorem skew_reduction_group : StepGroup := by
  intro k r i X hX
  exact ⟨glev_closed k r i, fun g hg t => glev_mul hg (exp_mem_glev hX t), exp_mem_glev hX⟩

end QnRdSkewW
