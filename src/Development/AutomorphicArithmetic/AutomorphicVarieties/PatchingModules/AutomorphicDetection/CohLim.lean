module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.FirstCohomologyBoundOfBoundaryBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KoszulThreeOfDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondCohomologyBoundOfBoundaryBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesFirstConditionAtLimitOfGroupCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesSecondConditionAtLimitOfGroupConditio
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

@[expose] public section

open UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem cohLim : CohLim := by
  intro l _ L G0 T Λ n x k al D0 _ hT he h1 h2
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG : TopFG Λ.G.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 _ Λ.πo Λ.πo_cont Λ.πo_surj
  exact ⟨firstCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k D0 hG (taylorWiles_first_condition_at_limit_of_group_condition l L G0 T Λ n x k D0 h1), secondCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k hG (taylorWiles_second_condition_at_limit_of_group_condition l L G0 T Λ n x k h2),
    koszulThree_of_det l L G0 T Λ n x k al hT he⟩

end UpperTheory.V.Pa
