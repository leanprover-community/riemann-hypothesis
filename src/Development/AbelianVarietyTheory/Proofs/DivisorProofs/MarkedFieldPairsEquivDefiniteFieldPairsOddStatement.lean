module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOdd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
