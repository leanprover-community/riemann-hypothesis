module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumReindexEquivalentSubtypes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOddStatement
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
import Mathlib.Tactic.Linter.Style
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem marked_field_pairs_sum_eq_definite_pairs_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel → ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → markedSumIrr G wt sel Kf f r K φ = dSumIrr G wt Kf f r K φ := by
  intro p _ G ha hn wt sel hsel Kf f r K φ hr hf hφ
  obtain ⟨e, he⟩ := GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd p G ha hn sel hsel
  unfold markedSumIrr dSumIrr
  convert GlobalTheory.finsum_ite_eq_of_equiv _ _ e (fun a : Cls G => wt (Quot.out a).pol * (Quot.out a).term Kf f r K φ)
    (fun b : DCls G => wt (Quot.out b).pol * (Quot.out b).term Kf f r K φ) fun q => by
    obtain ⟨hpol, hterm⟩ := he q
    show wt (Quot.out (e q).1).pol * (Quot.out (e q).1).term Kf f r K φ = wt (Quot.out q.1).pol * (Quot.out q.1).term Kf f r K φ
    rw [hpol, hterm Kf f r K φ hr hf hφ]

end GlobalTheory.LKDef
