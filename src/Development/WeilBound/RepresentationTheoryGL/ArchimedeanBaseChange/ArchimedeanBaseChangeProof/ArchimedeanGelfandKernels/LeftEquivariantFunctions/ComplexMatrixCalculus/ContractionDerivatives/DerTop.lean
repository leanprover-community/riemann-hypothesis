module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.SumSingleSmul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.CxbDer

open PositivityTheory.RgBcC

variable {n : ℕ}

def Gpi (g : X n) : Finset (Md n) → Finset (Md n) → ℂ := fun B' A => F (fb n A) g B'

theorem gamM_fun : (fun g : X n => (gamM (n := n) (Matrix.of g) : Finset (Md n) → Finset (Md n) → ℂ)) = Gpi := by
  funext g B' A
  simp only [gamM, matL, Gpi, F, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, Module.Basis.equivFun_apply]

theorem Gpi_contDiff : ContDiff ℂ ∞ (Gpi (n := n)) :=
  contDiff_pi.2 fun B' => contDiff_pi.2 fun A => contDiff_pi.1 (key (fb n A)).1 B'

def Lpi (n : ℕ) : X n →L[ℂ] (Finset (Md n) → Finset (Md n) → ℂ) :=
  ContinuousLinearMap.pi fun B' => ContinuousLinearMap.pi fun A =>
    (ContinuousLinearMap.proj B').comp (Classical.choose (key (n := n) (fb n A)).2)

theorem Gpi_hasFDerivAt : HasFDerivAt (Gpi (n := n)) (Lpi n) (one' n) := by
  refine hasFDerivAt_pi.2 fun B' => ?_
  refine hasFDerivAt_pi.2 fun A => ?_
  have h := (Classical.choose_spec (key (n := n) (fb n A)).2).1
  exact (hasFDerivAt_pi'.1 h) B'

theorem Lpi_apply (B : X n) (B' A : Finset (Md n)) :
    Lpi n B B' A = (fb n).equivFun (Dop B (fb n A)) B' := by
  simp only [Lpi, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [(Classical.choose_spec (key (n := n) (fb n A)).2).2 B]

theorem matL_Dop (B : X n) : (matL n (Dop B) : Finset (Md n) → Finset (Md n) → ℂ) =
    fun B' A => (fb n).equivFun (Dop B (fb n A)) B' := by
  funext B' A
  simp only [matL, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]

theorem matL_Ers (r s : Md n) : matL n (Ers r s) = creL n (Pi.single r 1) * annL n (Pi.single s 1) := by
  simp only [Ers, matL, creL, annL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact LinearMap.toMatrix_mul _ _ _

theorem matL_Dop_sum (B : X n) : matL n (Dop B) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by

  simp only [Dop, map_sum, map_smul, matL_Ers]

end PositivityTheory.RgBcC.CxbDer

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxbDer

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Lpi_eq {n : ℕ} (B : Matrix (Md n) (Md n) ℂ) :
    (Lpi n B : Finset (Md n) → Finset (Md n) → ℂ) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  exact (funext fun B' => funext fun A => Lpi_apply B B' A).trans ((matL_Dop B).symm.trans (matL_Dop_sum B))

theorem gamM_hasFDerivAt (n : ℕ) : ∃ L : type_of% (fderiv ℂ (gamM (n := n)) 1), HasFDerivAt (gamM (n := n)) L 1 ∧
    ∀ B : Matrix (Md n) (Md n) ℂ, L B = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  refine ⟨Lpi n, ?_, Lpi_eq⟩
  have h := Gpi_hasFDerivAt (n := n)
  rw [← gamM_fun] at h
  have h1 : (1 : Matrix (Md n) (Md n) ℂ) = one' n := by
    ext i j
    simp [one', Matrix.one_apply]
  rw [h1]
  exact h

theorem gamM_contDiff (n : ℕ) : ContDiff ℂ ∞ (gamM (n := n)) := by
  have h := Gpi_contDiff (n := n)
  rw [← gamM_fun] at h
  exact h

theorem gamDer : GamDer := by
  intro n
  obtain ⟨L, hL, hv⟩ := gamM_hasFDerivAt n
  refine ⟨gamM_contDiff n, fun B => ?_⟩
  rw [hL.fderiv, hv B]

end

end PositivityTheory.RgBcC
