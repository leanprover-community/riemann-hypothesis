module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumGl2FirstColumnUnitSetSuccFibre
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

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

theorem _root_.GlobalTheory.T.sum_gl2FirstColumnUnitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  first | exact @GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | exact GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre | (intros; apply GlobalTheory.KummerEisensteinGalois.sum_unitSet_succ_fibre <;> assumption)
