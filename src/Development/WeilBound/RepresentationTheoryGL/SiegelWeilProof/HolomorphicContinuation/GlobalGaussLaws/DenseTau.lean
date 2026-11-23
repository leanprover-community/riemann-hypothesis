module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseC
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Formalism.IndefR.Eqv (psiT thetaC)

theorem denseTau : DenseTau := by
  intro D n θ τ ι hθ hι y O hO hy
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hcl := DenseP.gam_dense (D := D) DenseP.genSt τ y
  obtain ⟨y', hy'O, γ, hγ, hγe⟩ := mem_closure_iff.1 hcl O hO hy
  have hc : ∀ τ' (w : Formalism.IndefR.Datum.Mx D (n + n) (n + n)), compAt (thetaC D) τ' w = w.map (psiT D τ') :=
    fun _ _ => rfl
  have hy' : (mat (ι y')).map (psiT D τ) = Glob.reidx (mR y') := (hc τ _).symm.trans (hι.2 y').1
  refine ⟨γ, hγ, y', hy'O, γ * (ι y')⁻¹, by group, fun y'' => ?_⟩
  have hR : (mat (γ * (ι y')⁻¹)).map (psiT D τ) = 1 := by
    have h1 : (mat γ).map (psiT D τ) = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (mat (ι y')).map (psiT D τ) := by
      rw [← Matrix.map_mul, ← DenseP.mat_mul, inv_mul_cancel_right]
    rw [hγe, hy'] at h1
    have h2 : Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹) = 1 := by
      rw [← DenseP.reidx_mul]
      show Glob.reidx (mR (y' * y'⁻¹)) = 1
      rw [mul_inv_cancel]; exact DenseP.reidx_one
    calc (mat (γ * (ι y')⁻¹)).map (psiT D τ)
        = (mat (γ * (ι y')⁻¹)).map (psiT D τ) * (Glob.reidx (mR y') * Glob.reidx (mR y'⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, ← h1, h2]
  generalize γ * (ι y')⁻¹ = x at hR ⊢
  apply Subtype.ext
  apply Units.ext
  show mat (x * ι y'') = mat (ι y'' * x)
  rw [DenseP.mat_mul, DenseP.mat_mul]
  apply Formalism.IndefR.Eqv.mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases h : τ' = τ
    · subst h; rw [hR]; simp only [Matrix.one_mul, Matrix.mul_one]
    · have h1 : (mat (ι y'')).map (psiT D τ') = 1 := by rw [← hc]; exact (hι.2 y'').2.1 τ' h
      rw [h1]; simp only [Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 y'').2.2]; simp only [Matrix.one_mul, Matrix.mul_one]

end PositivityTheory.Rg.Sw.Glob
