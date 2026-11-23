module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneIffOfSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneModEqOneAndOfDvd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_host : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  intro R H M p _ h
  obtain ⟨π, hN, hB, hA⟩ := h
  have h' : GlobalTheory.Mem.An.NormOne H.d M p := ⟨π.1, π.2, hN, hB, hA⟩
  exact ⟨(GlobalTheory.Mem.An.normOne_iff_host R H M p).1 h',
    (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd H.d M p (by have := H.hyp.2.2.2.1; omega) h').1⟩

end GlobalTheory.EX
