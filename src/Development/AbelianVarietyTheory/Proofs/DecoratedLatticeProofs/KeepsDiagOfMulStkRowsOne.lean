module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelEqLeviMulUnipotent
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SW

theorem keepsDiag_of_mul_stkRows_one {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    {β : Matrix (Fin n) (Fin n) R} (h : M * stkRows 1 1 = stkRows β β) : KeepsDiag finSumFinEquiv M := by
  rw [keepsDiag_iff]
  have key : ∀ s : Fin n ⊕ Fin n, ∀ j, M (finSumFinEquiv s) (finSumFinEquiv (Sum.inl j)) +
      M (finSumFinEquiv s) (finSumFinEquiv (Sum.inr j)) = β (s.elim id id) j := by
    intro s j
    have h1 : ∑ k, M (finSumFinEquiv s) k * stkRows (1 : Matrix (Fin n) (Fin n) R) 1 k j =
        stkRows β β (finSumFinEquiv s) j := congrFun (congrFun h _) j
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at h1
    simp only [stkRows, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    rw [h1]
    rcases s with s | s <;> rfl
  intro i j
  rw [key (Sum.inr i), key (Sum.inl i)]
  rfl

variable {D : D7}

section Core

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

end Core

end GlobalTheory.Core.Rk.SW
