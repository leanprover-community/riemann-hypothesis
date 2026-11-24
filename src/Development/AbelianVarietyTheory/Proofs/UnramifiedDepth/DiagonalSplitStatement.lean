module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplit
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
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.sum_hEnd_sub_hEnd_mem_logInt : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  first | exact @GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | exact GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | (intros; apply GlobalTheory.RowVal.MapSumDiagonal.diagonal_split <;> assumption)
