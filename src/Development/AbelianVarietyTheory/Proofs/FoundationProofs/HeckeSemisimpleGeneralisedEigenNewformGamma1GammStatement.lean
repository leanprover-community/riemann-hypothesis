module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSemisimpleGeneralisedEigenNewformGamma1Gamm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.hecke_semisimple_generalised_eigen_newform_gamma1Gamma0 : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k →
  ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
  α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
  ∀ (σT : ℕ → SL(2, ℤ)) (σD : (ZMod N)ˣ → SL(2, ℤ)),
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) (σT q)) →
    (∀ d : (ZMod N)ˣ, IsDiam N l (d : ZMod N) (σD d)) →
  ∀ z ∈ Z1 (Lev N l) (k - 2), ∀ n : ℕ,
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      ((TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    ((UlZ (Lev N l) (k - 2) l - α • 1) ^ n) z ∈ B1 (Lev N l) (k - 2) →
    (∀ d : (ZMod N)ˣ, ((DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      (TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) z ∈ B1 (Lev N l) (k - 2)) ∧
    (UlZ (Lev N l) (k - 2) l - α • 1) z ∈ B1 (Lev N l) (k - 2) ∧
    (∀ d : (ZMod N)ˣ, (DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) z ∈ B1 (Lev N l) (k - 2)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | exact GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform | (intros; apply GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform <;> assumption)
