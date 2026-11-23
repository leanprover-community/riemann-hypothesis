module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPairStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnOpen

theorem latRow_ann_open : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∃ U : Set (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))),
    IsOpen U ∧ (0 : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) ∈ U ∧
    ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have hS : IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) := isSelfDualC_neg (sdG (i + 1) hi)
  have hT : IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := sdG i hi.le
  have hfin := GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) hS hT
  obtain ⟨U, hU, h0, hUA⟩ := hfin.opn
  refine ⟨U, hU, h0, fun u' hu' hfu' u hu => ?_⟩
  have hu'R : u' ∈ latRow G i := hUA u' hu' hfu'
  have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ hS hT (fun _ => True) u (hfin.fin u hu)).1 hu.1 u' hu'R.1
  have e : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) u u' = -symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u' := by
    have hinv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E), (-A)⁻¹ = -A⁻¹ := by
      intro n A
      by_cases h : IsUnit A.det
      · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
      · have h' : ¬ IsUnit (-A).det := by
          rw [Matrix.det_neg]
          intro hu
          exact h (isUnit_of_mul_isUnit_right hu)
        rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]
    simp only [symplO, hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rw [e, AddChar.map_neg_eq_inv] at key
  exact inv_eq_one.mp key

end GlobalTheory.AscFin.AnnOpen

end
