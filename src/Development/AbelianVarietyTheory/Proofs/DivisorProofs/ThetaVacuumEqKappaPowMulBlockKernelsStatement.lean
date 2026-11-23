module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK → ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  first | exact @GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | exact GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | (intros; apply GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB <;> assumption)
