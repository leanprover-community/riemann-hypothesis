module

public import Formalism.CoboundaryTransfers.StatementAPI
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.CoboundaryTransfers

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]

end SlopeTestRemainingChoices

theorem finiteClassesLift_holds : LiftHf := by
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g eW c
    hnat hcl₁ hint hlifts κ hκ
  obtain ⟨pr, hcoc, hpr⟩ := hint.2 κ hκ
  obtain ⟨y₁, z₁, hcoc₁, hy, hz⟩ := hlifts _ _ hcoc
  have hmem : ((y₁, z₁) : D₁ × D₁) ∈ W₁.Z1 := (WachMod.mem_cocycles_units_iff W₁ _).mpr hcoc₁.2
  refine ⟨cl₁ ⟨(y₁, z₁), hmem⟩, hcl₁ _ hcoc₁, ?_⟩
  have hpr' : ((c • pr : W₂.Z1) : D₂ × D₂) = S.π.f2 (⟨(y₁, z₁), hmem⟩ : W₁.Z1) := by
    show c • (pr : D₂ × D₂) = (S.π.f y₁, S.π.f z₁)
    rw [hy, hz]
    rfl
  rw [hnat _ _ hpr', map_smul, hpr, smul_smul, mul_comm]

end Formalism.CoboundaryTransfers
