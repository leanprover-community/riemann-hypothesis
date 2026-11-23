module

public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspaces
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  first | exact @GlobalTheory.IdemRange.limit_idempotent_range | exact GlobalTheory.IdemRange.limit_idempotent_range | (intros; apply GlobalTheory.IdemRange.limit_idempotent_range <;> assumption)
