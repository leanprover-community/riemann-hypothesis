module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DifferentiableAtOm

@[expose] public section

open NumberField Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.Z.Bc

open UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.HV UpperTheory.V.Lit

theorem cyclicLiftRankTwo_of_cyclic_base_change (h : CycC) : CyclicBaseChangeLiftRankTwo := by
  intro F E _ _ hF _ _ hE _ _ hp π hr
  rcases (h F E hp hF 2 one_le_two).1 _ _ (Or.inl ⟨hF, π, rfl, rfl⟩)
    (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (GlobalTheory.CuspRep.CG.mk π) τ, hr τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
  · exact Or.inl h1
  · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
    · exact Or.inr ⟨P, hi, hw⟩
    · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
      exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (hE.isComplex v))

end UpperTheory.V.Z.Bc
