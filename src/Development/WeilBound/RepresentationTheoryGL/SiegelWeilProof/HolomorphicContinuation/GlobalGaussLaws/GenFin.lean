module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinSt
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

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GenFinH

variable {n : ℕ}

theorem blkDm_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (blkDm M).map f = blkDm (M.map f) := by
  ext i j; rfl

theorem blkDm_one {R : Type} [CommRing R] : blkDm (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  unfold blkDm
  rw [Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]

theorem det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) :
    f M.det = (M.map f).det := by
  rw [RingHom.map_det]; rfl

end PositivityTheory.Rg.Sw.Glob.GenFinH

namespace PositivityTheory.Rg.Sw.Glob

open GenFinH

theorem kInFin_of (hU : UnitD) (hL : LocFin) (hGL : GlueLevi) (hGW : GlueW) (hUA : UnitAE) : KInFin := by
  intro D n k hk hreal
  choose a I hgood using fun v => hL D n k hk v
  obtain ⟨m, hm, hmv, hmr⟩ := hGL D n a (fun v => (hgood v).1) (fun v => (hgood v).2.1)
  obtain ⟨w, hw, hwv, hwr⟩ := hGW D n I
  have hmat : ∀ {S : Type} [CommRing S] (f : AE D →+* S), (mat (k * m * w)).map f = (mat k).map f * (mat m).map f * (mat w).map f := by
    intro S _ f
    show (mat k * mat m * mat w).map f = _
    rw [Matrix.map_mul, Matrix.map_mul]
  have hd : IsUnit (blkDm (mat (k * m * w))).det := by
    apply hUA D
    · intro τ
      rw [det_map, blkDm_map, hmat, hreal τ, hmr τ, hwr τ, Matrix.mul_one, Matrix.mul_one, blkDm_one, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [det_map, blkDm_map, hmat, hmv v, hwv v]
      exact (hgood v).2.2
  have h1 : k * m * w ∈ Subgroup.closure (genSet D n) := hU D n _ hd
  have hm' : m ∈ Subgroup.closure (genSet D n) := Subgroup.subset_closure hm
  have e : k = k * m * w * w⁻¹ * m⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hm')

end PositivityTheory.Rg.Sw.Glob
