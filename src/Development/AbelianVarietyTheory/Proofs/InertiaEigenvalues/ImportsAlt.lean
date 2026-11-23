module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

namespace GlobalTheory.TargetStatementAlt

open Polynomial

theorem main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by
  let f : F →ₐ[R] AlgebraicClosure F := IsScalarTower.toAlgHom R F (AlgebraicClosure F)
  let φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F) := f.mapMatrix
  obtain ⟨p, hpm, hp⟩ := hM.map φ
  have key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.mp hμ).2
    have hs : μ ∈ spectrum (AlgebraicClosure F) (φ M) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F)))
      ⟨μ, hs, rfl⟩
    have h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h2, spectrum.mem_iff, sub_zero] at h1
    refine ⟨p, hpm, ?_⟩
    by_contra hne
    apply h1
    have : eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0 := by
      rwa [eval_map_algebraMap, aeval_def]
    exact (Ne.isUnit this).map _
  have ht : IsIntegral R (Matrix.trace (φ M)) := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum key
  have he : Matrix.trace (φ M) = f (Matrix.trace M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]
  rw [he] at ht
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ht

theorem target : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h

end GlobalTheory.TargetStatementAlt
