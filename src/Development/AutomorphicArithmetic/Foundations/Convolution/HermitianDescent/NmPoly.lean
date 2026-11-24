module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)

private theorem sg_succ (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg (σ ^ m) (sg σ x) := by
  rw [pow_succ]
  rfl

private theorem sg_succ' (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg σ (sg (σ ^ m) x) := by
  rw [pow_succ']
  rfl

private theorem sg_one (x : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) x = x := rfl

private theorem nm_succ (m : ℕ) (δ : GL (Fin n) R) : nm σ (m + 1) δ = nm σ m δ * sg (σ ^ m) δ := by
  simp [nm, List.range_succ]

private theorem nm_conj (m : ℕ) (x δ : GL (Fin n) R) : nm σ m (sgConj σ x δ) = x⁻¹ * nm σ m δ * sg (σ ^ m) x := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]
    group

private theorem sg_nm (m : ℕ) (δ : GL (Fin n) R) : sg σ (nm σ m δ) = δ⁻¹ * nm σ m δ * sg (σ ^ m) δ := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, map_mul, ih, ← sg_succ']
    group

end

theorem UpperTheory.ConvolutionTheory.D.nmPoly :
    UpperTheory.ConvolutionTheory.D.NmPoly := by
  intro k R _ _ _ σ q h n δ
  refine ⟨?_, fun x => by rw [nm_conj, h.pow, sg_one]⟩
  have e : (cp (nm σ q δ)).map (σ : R →+* R) = cp (nm σ q δ) := by
    have h1 := sg_nm σ q δ
    rw [h.pow, sg_one] at h1
    have h2 : cp (sg σ (nm σ q δ)) = (cp (nm σ q δ)).map (σ : R →+* R) := Matrix.charpoly_map _ _
    rw [← h2, h1, cp, cp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hl : cp (nm σ q δ) ∈ Polynomial.lifts (algebraMap k R) := (Polynomial.lifts_iff_coeff_lifts _).2 fun i =>
    h.fix _ (by simpa [Polynomial.coeff_map] using congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) e)
  obtain ⟨p, hp⟩ := hl
  exact ⟨p, Polynomial.monic_of_injective h.inj (by rw [show p.map (algebraMap k R) = _ from hp]; exact Matrix.charpoly_monic _), hp.symm⟩
