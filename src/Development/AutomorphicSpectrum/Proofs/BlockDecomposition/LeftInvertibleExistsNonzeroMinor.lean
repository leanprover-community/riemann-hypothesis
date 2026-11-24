module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldA

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem det_mul_eq_sum_mnr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R) :
    (L * M).det = ∑ g : Fin n → ι, (∏ i, L i (g i)) * mnr M g := by
  have h1 : (L * M).det =
      (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap
        (fun i => ∑ j, L i j • M j) := by
    have : (L * M) = Matrix.of (fun i => ∑ j, L i j • M j) := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    rfl

  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem exists_mnr_ne_zero_of_left_inverse :
    ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
      (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
      L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  intro R _ _ ι _ _ n M L h
  by_contra hc
  push_neg at hc
  have key := det_mul_eq_sum_mnr M L
  rw [h, Matrix.det_one] at key
  simp [hc] at key

end GlobalTheory.CompanionTheory.GodementH
