module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = ⟨0, ha⟩
    · subst i; simpa [d] using hzz
    · simp [d, hi]
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
