module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZero
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

open scoped Matrix

theorem _root_.GlobalTheory.T.normCompatible_system_frobenius_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  first | exact @GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | exact GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | (intros; apply GlobalTheory.NormSystemVanishing.normCompatible_eq_zero <;> assumption)
