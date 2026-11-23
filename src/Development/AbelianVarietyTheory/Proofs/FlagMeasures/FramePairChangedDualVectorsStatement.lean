module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairChangedDualVectors
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

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.framePair_changed_dualVectors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  first | exact @GlobalTheory.HL.ToC.changed_duals | exact GlobalTheory.HL.ToC.changed_duals | (intros; apply GlobalTheory.HL.ToC.changed_duals <;> assumption)
