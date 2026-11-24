module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspidalAtAllCuspsSL2SlashIntMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix : ∀ (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (G : ℍ → ℂ), 0 < M.det → CuspAll k G → CuspAll k (G ∣[k] toGL M) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | exact GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspAll_slash_toGL <;> assumption)
