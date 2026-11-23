module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localMove_classRep_iff_localConditions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m →
    ∀ (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1),
    LocMv I u a i c s κ ↔ ((I.stp u a i).gam c.1 κ = 1 ∧
      cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
      LocalCondMoveDecoratedLattice u (B.R.N i) s κ.2.1.1 ∧ LocCQ (I.Q a) (B.R.N i) s κ.2.2.1) := by
  exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff
