module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRedField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

abbrev Ev (D : D7) (v : GlobalTheory.FinPl.Pl D) := Fv D.host.F v ⊗[D.host.F] D.host.E

def IsIntUnit {D : D7} {v : GlobalTheory.FinPl.Pl D} (z : Ev D v) : Prop :=
  z ∈ intLoc D.host.F D.host.E v ∧ ∃ z' ∈ intLoc D.host.F D.host.E v, z * z' = 1

def cTv {D : D7} {v : GlobalTheory.FinPl.Pl D} (a : Matrix (Fin n) (Fin n) (Ev D v)) : Matrix (Fin n) (Fin n) (Ev D v) :=
  (a.map (sigR (Fv D.host.F v) D.sp.cm.sig)).transpose

def LocGood {D : D7} {v : GlobalTheory.FinPl.Pl D} (kv : Matrix (Fin (n + n)) (Fin (n + n)) (Ev D v))
    (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)) : Prop :=
  (∀ i j, a i j ∈ intLoc D.host.F D.host.E v) ∧ IsIntUnit a.det ∧
    IsIntUnit (blkDm (kv * blk4 a 0 0 (cTv a)⁻¹ * wIm I)).det

def LocFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, ∀ v : GlobalTheory.FinPl.Pl D,
    ∃ (a : Matrix (Fin n) (Fin n) (Ev D v)) (I : Finset (Fin n)), LocGood ((mat k).map (GlobalTheory.FinPl.compAt D v)) a I

def GlueLevi : Prop :=
  ∀ (D : D7) (n : ℕ) (a : ∀ v : GlobalTheory.FinPl.Pl D, Matrix (Fin n) (Fin n) (Ev D v)),
    (∀ v i j, a v i j ∈ intLoc D.host.F D.host.E v) → (∀ v, IsIntUnit (a v).det) →
    ∃ m : G D n, m ∈ genSet D n ∧ (∀ v, (mat m).map (GlobalTheory.FinPl.compAt D v) = blk4 (a v) 0 0 (cTv (a v))⁻¹) ∧
      ∀ τ, (mat m).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def GlueW : Prop :=
  ∀ (D : D7) (n : ℕ) (I : GlobalTheory.FinPl.Pl D → Finset (Fin n)),
    ∃ w ∈ Subgroup.closure (genSet D n), (∀ v, (mat w).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)) ∧
      ∀ τ, (mat w).map (Formalism.IndefR.Eqv.psiT D τ) = 1

def UnitAE : Prop :=
  ∀ (D : D7) (d : AE D), (∀ τ, Formalism.IndefR.Eqv.psiT D τ d ≠ 0) → (∀ v, IsIntUnit (GlobalTheory.FinPl.compAt D v d)) → IsUnit d

end PositivityTheory.Rg.Sw.Glob
