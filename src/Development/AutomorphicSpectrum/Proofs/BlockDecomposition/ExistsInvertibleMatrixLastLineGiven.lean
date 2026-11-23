module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import GroundTheory.LocalFields.Interface

@[expose] public section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

private theorem det_updateRow_one' {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (r : n) (b : n → R) : (updateRow (1 : Matrix n n R) r b).det = b r := by
  rw [← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl

theorem exists_GL_lastRow_eq (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hN : (updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_updateRow_one']
    simpa using hi
  have hM : ((updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m))).submatrix id (Equiv.swap i (Fin.last m))).det ≠ 0 := by
    rw [det_permute']
    refine mul_ne_zero ?_ hN
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i (Fin.last m))) with h | h <;> simp [h]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show updateRow (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m)
      (a ∘ Equiv.swap i (Fin.last m)) (Fin.last m) (Equiv.swap i (Fin.last m) j) = a j
  rw [updateRow_self, Function.comp_apply, Equiv.swap_apply_self]

end GlobalTheory.CompanionTheory.MirFourier
