module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧ κ.ker = (cycU l U).subgroupOf U ∧
        κ γ = Multiplicative.ofAdd 1 ∧ U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧ ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUg hu
    simp only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h
    exact h.2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := by
    intro h
    apply hUk
    intro u hu
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    exact hχc.comp continuous_subtype_val
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := by
    intro x
    have h1 : κ x = e (ψ x) := rfl
    rw [h1, map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hSc : IsClosed S := hVc.preimage continuous_subtype_val
    have hIc : IsClosed (κ '' S) := (hSc.isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := Multiplicative.ofAdd ⁻¹' (κ '' S)
    have hTc : IsClosed T := hIc.preimage continuous_ofAdd
    have hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T := by
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    have hT : T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← PadicInt.denseRange_intCast.closure_range]
      exact closure_minimal hTz hTc
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hks' : κ s = κ ⟨u, hu⟩ := hks
    have hq : κ (⟨u, hu⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hks', mul_inv_cancel]
    have hq' := (hkκ _).mp hq
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V := by
      apply hsub
      apply Subgroup.mem_sup_right
      simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩
    have hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) := by
      simp
    rw [hu']
    exact V.mul_mem hmem hs
  · intro hfin
    have hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l) := ⟨γ.1, γ.2, rfl⟩
    have h1 := (hkκ γ).mpr (htor _ hm hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
