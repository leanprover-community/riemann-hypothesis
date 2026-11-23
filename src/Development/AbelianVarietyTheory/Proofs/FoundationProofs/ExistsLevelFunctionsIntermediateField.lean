module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeKer
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _


open GlobalTheory.FN.LevelGal in
theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
