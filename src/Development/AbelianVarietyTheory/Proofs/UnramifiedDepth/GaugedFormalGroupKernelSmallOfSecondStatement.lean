module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond
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
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  first | exact @GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | exact GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition | (intros; apply GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition <;> assumption)
