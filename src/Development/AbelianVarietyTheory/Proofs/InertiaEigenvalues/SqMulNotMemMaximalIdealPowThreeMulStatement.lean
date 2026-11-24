module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqMulNotMemMaximalIdealPowThreeMul
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.sq_mul_not_mem_maximalIdeal_pow_three_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ), p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c → ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  first | exact @GlobalTheory.PMon.Ram.sq_mul_not_mem_maxIdeal_pow | exact GlobalTheory.PMon.Ram.sq_mul_not_mem_maxIdeal_pow | (intros; apply GlobalTheory.PMon.Ram.sq_mul_not_mem_maxIdeal_pow <;> assumption)
