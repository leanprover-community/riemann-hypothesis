module

public import GroundTheory.ProfiniteCohomology.LocalClassFormation.InvariantDefs
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflationDefs
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflation
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FinrankLeNatCardGroupCohomologyTwoGalUnits
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
import Mathlib.Tactic.PNatToNat

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Self

variable (K M : Type) [Field K] [Field M] [Algebra K M]

theorem unitsRes_self (n : ℕ) : unitsRes K K M n = 𝟙 _ := by
  rw [unitsRes, ← groupCohomology.map_id]
  exact groupCohomology.map_congr (by ext; rfl) rfl n

end Self

variable (F Ω : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension F Ω]

theorem unramifiedLevelInv_unitsInflationOfLE {m n : ℕ+} (h : (m : ℕ) ∣ n)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2) :
    unramifiedLevelInv F Ω n ((unitsInflationOfLE (unramifiedLevel_le F Ω h) 2).hom y) =
      unramifiedLevelInv F Ω m y := by
  let _ : Algebra (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    (IntermediateField.inclusion (unramifiedLevel_le F Ω h)).toRingHom.toAlgebra
  have : IsScalarTower F (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : ValuativeExtension (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) :=
    IntermediateField.valuativeExtension_inclusion _
  have key : unitsInflationOfLE (unramifiedLevel_le F Ω h) 2 =
      unitsInfl F (unramifiedLevel F Ω m) (unramifiedLevel F Ω n) 2 ≫
        unitsRes F F (unramifiedLevel F Ω n) 2 := by
    rw [unitsRes_self, Category.comp_id]
    rfl
  rw [unramifiedLevelInv_apply, unramifiedLevelInv_apply, key,
    h2GalUnitsAddEquiv_unitsRes_unitsInfl, unramifiedInv_inflation]

theorem unramifiedLevelInv_eq_of_brauerInflation_eq {m n : ℕ+}
    {y : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2}
    {z : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2}
    (h : (brauerInflation (unramifiedLevel F Ω m)).hom y =
      (brauerInflation (unramifiedLevel F Ω n)).hom z) :
    unramifiedLevelInv F Ω m y = unramifiedLevelInv F Ω n z := by
  have hm : ((m : ℕ)) ∣ ((m * n : ℕ+) : ℕ) := ⟨n, by simp⟩
  have hn : ((n : ℕ)) ∣ ((m * n : ℕ+) : ℕ) := ⟨m, by simp [mul_comm]⟩
  have hinj := brauerInflation_injective (L := Ω) (unramifiedLevel F Ω (m * n))
  have heq : (unitsInflationOfLE (unramifiedLevel_le F Ω hm) 2).hom y =
      (unitsInflationOfLE (unramifiedLevel_le F Ω hn) 2).hom z := by
    apply hinj
    have e1 := congrArg (fun φ => φ.hom y)
      (unitsInflationOfLE_comp_unitsInflation (L := Ω) (unramifiedLevel_le F Ω hm) 2)
    have e2 := congrArg (fun φ => φ.hom z)
      (unitsInflationOfLE_comp_unitsInflation (L := Ω) (unramifiedLevel_le F Ω hn) 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
    rw [e1, e2]
    exact h
  rw [← unramifiedLevelInv_unitsInflationOfLE F Ω hm y, heq,
    unramifiedLevelInv_unitsInflationOfLE F Ω hn z]

theorem brauerInvFun_brauerInflation (n : ℕ+)
    (y : groupCohomology (galUnits F (unramifiedLevel F Ω n)) 2) :
    brauerInvFun F Ω ((brauerInflation (unramifiedLevel F Ω n)).hom y) =
      unramifiedLevelInv F Ω n y := by
  have hex : ∃ (m : ℕ+) (z : groupCohomology (galUnits F (unramifiedLevel F Ω m)) 2),
      (brauerInflation (unramifiedLevel F Ω m)).hom z =
        (brauerInflation (unramifiedLevel F Ω n)).hom y := ⟨n, y, rfl⟩
  rw [brauerInvFun, dite_eq_left hex]
  exact unramifiedLevelInv_eq_of_brauerInflation_eq F Ω hex.choose_spec.choose_spec

end GroundTheory.ProfCoh
