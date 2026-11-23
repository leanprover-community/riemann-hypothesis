module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegral
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_basis_change_integral : ∀ (K : Type) [Field K] (R : Subring K) [IsLocalRing R] (r : ℕ) (g : Fin r → Fin r → K), (∀ k : Fin r, ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K g ((k : ℕ) + 1)) → ∃ P : Matrix (Fin r) (Fin r) K, (∀ a b, P a b ∈ R) ∧ P.det ≠ 0 ∧ P.det⁻¹ ∈ R ∧ ∀ i, flagStep K (fun k a => P a k) i = flagStep K g i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Adapted.exists_adapted <;> assumption)
