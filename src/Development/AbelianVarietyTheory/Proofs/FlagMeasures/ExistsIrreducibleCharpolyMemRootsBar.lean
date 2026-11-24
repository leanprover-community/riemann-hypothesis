module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem exists_irreducible_charpoly_mem_rootsBar (g : ℕ) [Fact g.Prime] (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ≠ 0) (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible (y : Mt g d).charpoly ∧
      z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly := by
  subst hd
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ Formalism.CyclotomicNorms.rootsBar M.charpoly
    rw [hM, Formalism.CyclotomicNorms.rootsBar, mem_roots_map (minpoly.ne_zero hi), ← aeval_def]
    exact minpoly.aeval _ _

end GlobalTheory.GLm
