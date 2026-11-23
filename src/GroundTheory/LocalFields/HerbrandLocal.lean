module

public import GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.LocalFields.CompleteTrivialLocal
public import GroundTheory.LocalFields.HerbrandCyclic
public import GroundTheory.LocalFields.HerbrandLocalBase
public import GroundTheory.LocalFields.HilbertCyclic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in
theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in
theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h

theorem natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by
  rw [← natCard_tateZero_units_eq]
  exact natCard_tateZero_units

end GroundTheory.LocalField
