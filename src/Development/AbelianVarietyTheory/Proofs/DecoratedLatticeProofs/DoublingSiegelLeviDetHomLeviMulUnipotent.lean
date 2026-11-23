module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

namespace GlobalTheory.Core.Rk.SWLaw

theorem aP_levi_mul_nC : ∀ (D : D7) (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c → aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A p a c hp
  have hM : Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) ⬝ (dblDec A).jX = (dblDec A).jX ⬝ a.1 := by
    rw [hp, GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, HypDec.nC_jX, HypDec.levi_jX]
  apply Units.ext
  rw [GlobalTheory.Doubling.val_aOf]
  show (GlobalTheory.Doubling.leviMat finSumFinEquiv (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  set M := Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A)) with hMdef
  have key : GlobalTheory.Doubling.leviMat finSumFinEquiv M * rat A.gram⁻¹ = rat A.gram⁻¹ * a.1 := by
    ext i j
    have h := congrFun (congrFun hM (finSumFinEquiv (Sum.inl i))) j
    simp only [HypDec.jX, dblDec, rat, stackRows, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Fin.sum_univ_add, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, id] at h
    simp only [GlobalTheory.Doubling.leviMat, rat, Matrix.mul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.of_apply, Matrix.submatrix_apply, Matrix.map_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      add_mul, Finset.sum_add_distrib]
    exact h
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_nonsing_inv_det _ (gram_det_ne A).isUnit).map _
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  exact hu.mul_left_cancel hd

end GlobalTheory.Core.Rk.SWLaw
