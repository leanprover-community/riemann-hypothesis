module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_count :
    ∀ {K G W V T : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W] [Module.Finite K W] [AddCommGroup T] [Module K T] [Module.Finite K T] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation K G W) (b : V → Submodule K W) (φ : T →ₗ[K] (G → W)), (∀ v Y, (∀ s, ρ (loc v s) Y - Y ∈ b v) → Y ∈ b v) → (∀ x ∈ Z1C loc ρ b, ∃ D X, ∀ s, φ D s = x.1 s + (ρ s X - X)) → Module.finrank K (H1C loc ρ b) ≤ Module.finrank K T ∧ ∀ (X₀ : W) (D₀ : T), X₀ ≠ 0 → (∀ s, φ D₀ s = ρ s X₀ - X₀) → Module.finrank K (H1C loc ρ b) + 1 ≤ Module.finrank K T + Module.finrank K (coneH0 ρ b) := by
  intro K G W V T _ _ _ _ _ _ _ _ _ Gv _ loc ρ b φ hA hB
  let cob : W →ₗ[K] (G → W) := LinearMap.pi (fun s => ρ s - LinearMap.id)
  have hcob : ∀ X s, cob X s = ρ s X - X := fun X s => rfl
  let C := LinearMap.range cob
  let f : T →ₗ[K] (G → W) ⧸ C := C.mkQ ∘ₗ φ
  let Ψ : Z1C loc ρ b →ₗ[K] (G → W) ⧸ C :=
    C.mkQ ∘ₗ (LinearMap.fst K (G → W) (V → W)) ∘ₗ (Z1C loc ρ b).subtype
  have hle : Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hx⟩ hxB
    rw [Submodule.mem_comap] at hxB
    obtain ⟨X, hX, -⟩ := hxB
    rw [LinearMap.mem_ker]
    show C.mkQ x.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X, funext fun s => ((hX s).trans (hcob X s).symm).symm⟩
  have hker : LinearMap.ker Ψ ≤ Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) := by
    rintro ⟨x, hx⟩ hk
    rw [LinearMap.mem_ker] at hk
    change C.mkQ x.1 = 0 at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
    obtain ⟨X, hX⟩ := hk
    obtain ⟨-, -, hloc⟩ := hx
    rw [Submodule.mem_comap]
    refine ⟨X, fun s => (congrFun hX s).symm, fun v => ?_⟩
    have hmem : X - x.2 v ∈ b v := by
      refine hA v _ (fun s => ?_)
      have h1 := hloc v s
      convert h1 using 1
      rw [← hX, hcob, map_sub]
      abel
    have h2 := (b v).neg_mem hmem
    rwa [neg_sub] at h2
  let L := (Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b)).liftQ Ψ hle
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : ∀ y, L y ∈ LinearMap.range f := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨D, X, hD⟩ := hB z.1 z.2
    refine ⟨D, ?_⟩
    show C.mkQ (φ D) = C.mkQ z.1.1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨X, funext fun s => ?_⟩
    show cob X s = φ D s - z.1.1 s
    rw [hcob, hD]
    abel
  let L' : H1C loc ρ b →ₗ[K] LinearMap.range f := L.codRestrict _ hrange
  have hinj' : Function.Injective L' := fun a c h => hinj (congrArg Subtype.val h)
  have h1 : Module.finrank K (H1C loc ρ b) ≤ Module.finrank K (LinearMap.range f) :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := LinearMap.finrank_range_le f
  refine ⟨h1.trans h3, ?_⟩
  intro X₀ D₀ hX₀ hD₀
  by_cases hinv : ∀ s, ρ s X₀ = X₀
  · have hH0 : X₀ ∈ coneH0 ρ b := by
      show (∀ g, ρ g X₀ = X₀) ∧ ∀ v, X₀ ∈ b v
      exact ⟨hinv, fun v => hA v X₀ (fun s => by rw [hinv, sub_self]; exact (b v).zero_mem)⟩
    have h4 : Module.finrank K (coneH0 ρ b) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hH0
      exact hX₀ ((Submodule.mem_bot K).1 hH0)
    omega
  · push_neg at hinv
    obtain ⟨s, hs⟩ := hinv
    have hD0 : D₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      show C.mkQ (φ D₀) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨X₀, funext fun t => (hcob X₀ t).trans (hD₀ t).symm⟩
    have hne : D₀ ≠ 0 := by
      rintro rfl
      apply hs
      have h5 := hD₀ s
      rw [map_zero, Pi.zero_apply] at h5
      exact (sub_eq_zero.1 h5.symm)
    have h4 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hD0
      exact hne ((Submodule.mem_bot K).1 hD0)
    omega
