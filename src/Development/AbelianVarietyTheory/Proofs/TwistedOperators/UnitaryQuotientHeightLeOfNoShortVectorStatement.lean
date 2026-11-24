module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVector
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C := by
  first | exact @GlobalTheory.HtMahler.quotHeight_le_of_no_short | exact GlobalTheory.HtMahler.quotHeight_le_of_no_short | (intros; apply GlobalTheory.HtMahler.quotHeight_le_of_no_short <;> assumption)
