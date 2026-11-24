module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentatives
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

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.termLevel_zero_and_bounded_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ (S.spanTo S.f j ⊔ S.spanTo S.f' j), y - y₁ ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y) ∧ ∀ (al al' : Fin (r + 1) → E) (j : ℕ), S.lev (S.fr d Λ) (S.fr' d Λ) (∑ i, al i • S.fr d Λ i + ∑ i, al' i • S.fr' d Λ i) ≤ j ↔ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  first | exact @GlobalTheory.HL.LevelRep.level_rep | exact GlobalTheory.HL.LevelRep.level_rep | (intros; apply GlobalTheory.HL.LevelRep.level_rep <;> assumption)
