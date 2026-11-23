module

public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrand
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import Mathlib.FieldTheory.KrullTopology
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.Unramified
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]


include v in
open AdicLiesOver in
theorem isZero_groupCohomology_decomposition_integerUnits
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (groupCohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletionIntegers L)ˣ) n) := by
  have := isUnramified_adicCompletion v w he
  have : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := finite_adicCompletion v w
  refine (isZero_groupCohomology_integerUnits (v.adicCompletion K) (w.adicCompletion L) hn).of_iso
    (groupCohomology.mapIso (decompositionMulEquiv v w) (integerUnitsAddEquiv w).toIntLinearEquiv
      (fun σ => LinearMap.ext fun x => integerUnitsAddEquiv_decomposition v w σ x) n)


include v in
theorem isZero_cohomology_decomposition_integerUnits
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) {n : ℕ} (hn : 1 ≤ n) :
    IsZero (cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletionIntegers L)ˣ) n) :=
  (isZero_groupCohomology_decomposition_integerUnits v w he hn).of_iso
    (cohomologyIsoGroupCohomology _ n)

end GroundTheory.ProfCoh
