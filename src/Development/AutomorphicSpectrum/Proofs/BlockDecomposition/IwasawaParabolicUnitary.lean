module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangular
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hk
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
