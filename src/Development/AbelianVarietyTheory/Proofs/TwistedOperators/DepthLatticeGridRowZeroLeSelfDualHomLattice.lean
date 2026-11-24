module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

theorem latRow_zero_le_latBig : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  intro D hq T L μ0 hL sc G W M hM him u hu
  have hS : IsSelfDualC (G.V (.grid (0 + 1) 0)) (G.Λ (.grid (0 + 1) 0)) :=
    (G.sp.V_is (0 + 1) 0 (by omega) him (by omega)).sd
  have hT : IsSelfDualC (G.V (.grid 0 0)) (G.Λ (.grid 0 0)) := by
    obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
    exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
  have h1 := idLat_one (G.Λ (.grid 0 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (0 + 1) 0))) (G.V (.grid 0 0)) (G.Λ (.grid (0 + 1) 0) : Set _)
      (G.Λ (.grid 0 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (0 + 1) 0)) (G.Λ (.grid 0 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (0 + 1) 0)) 1 (G.Λ (.grid 0 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
