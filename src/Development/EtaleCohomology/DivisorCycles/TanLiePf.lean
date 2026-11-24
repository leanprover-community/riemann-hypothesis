module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Mathlib.RingTheory.Derivation.Lie
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

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]

  simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
