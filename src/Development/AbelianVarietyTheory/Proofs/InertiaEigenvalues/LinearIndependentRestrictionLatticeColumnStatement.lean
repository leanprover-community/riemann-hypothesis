module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRestrictionLatticeColumn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.linearIndependent_restrictionLattice_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | exact GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil | (intros; apply GlobalTheory.PMon.ResR.eq_zero_of_sum_kd_mul_U0_mem_fil <;> assumption)
