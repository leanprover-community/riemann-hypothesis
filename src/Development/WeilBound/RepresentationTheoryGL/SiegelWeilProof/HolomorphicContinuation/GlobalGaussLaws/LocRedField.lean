module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
