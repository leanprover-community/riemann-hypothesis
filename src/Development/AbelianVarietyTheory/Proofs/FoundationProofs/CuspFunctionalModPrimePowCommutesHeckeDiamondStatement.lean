module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_hecke | exact GlobalTheory.CyclotomicQExpansion.thN_hecke | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_hecke <;> assumption)
