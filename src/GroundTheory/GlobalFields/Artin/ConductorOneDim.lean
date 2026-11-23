module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.TateThesis.LocalConductor
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import GroundTheory.GlobalFields.ClassFieldConsequences.ConductorLocal
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

open IdeleGroup


variable {k M : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M] [IsGalois k M]


section Units

open ValuativeRel

variable {K : Type*} [Field K] [NumberField K]

theorem unitFiltrationUnits_eq_unitsLevel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n = unitsLevel v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact unitFiltrationUnits_zero_eq_unitsLevel_zero v
  ext x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, GroundTheory.Global.mem_unitsLevel_of_one_le hn, ← map_pow,
    (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ,
    ← WithZero.exp_nsmul]
  simp

end Units


variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)


end GroundTheory.Global
