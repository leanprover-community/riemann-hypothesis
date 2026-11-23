module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField UpperTheory.V.Af

theorem UpperTheory.V.Af.solDescent :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.SolDescent := by
  intro H F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hsol hplus hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  have hM' : IsCMField M := hM.resolve_left fun h => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F M).isComplex v)) (h.isReal v)
  exact Z.Bc.solC H H.cyc F M Ω hsol hF hM' l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
