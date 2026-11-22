module

public import Mathlib
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional
public import GroundTheory.AutomorphicForms.HarishChandraRegularity
public import GroundTheory.AutomorphicForms.RealGroupsKAK

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

section Schur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem eq_algebraMap_of_commute [Nontrivial V] {S : Set (V →L[ℂ] V)}
    (hirr : ∀ W : Submodule ℂ V, IsClosed (W : Set V) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {A : V →L[ℂ] V} (hsa : IsSelfAdjoint A) (hcomm : ∀ s ∈ S, Commute A s) :
    ∃ c : ℝ, A = algebraMap ℝ (V →L[ℂ] V) c := by
  have hnt : Nontrivial (V →L[ℂ] V) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : V →L[ℂ] V => T v) h)⟩⟩
  have hsub : (spectrum ℝ A).Subsingleton := by
    intro a ha b hb
    by_contra hab
    wlog hlt : a < b generalizing a b
    · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
    set c := (a + b) / 2 with hc
    let f : ℝ → ℝ := fun x => max (x - c) 0
    let g : ℝ → ℝ := fun x => max (c - x) 0
    have hfc : Continuous f := by fun_prop
    have hgc : Continuous g := by fun_prop
    have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
      funext x
      rcases le_total x c with h | h
      · simp [f, max_eq_right (sub_nonpos.mpr h)]
      · simp [g, max_eq_right (sub_nonpos.mpr h)]
    have hQP : cfc g A * cfc f A = 0 := by
      rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
    have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
      intro φ hφ x hx hφx h
      have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
      have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
      rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
      exact hφx hmem
    have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
      simp only [f]; rw [max_eq_left (by linarith)]; linarith)
    have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
      simp only [g]; rw [max_eq_left (by linarith)]; linarith)
    have hPcomm : ∀ s ∈ S, Commute (cfc f A) s := fun s hs =>
      (hcomm s hs).cfc_real f
    set W := (LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V)).topologicalClosure with hW
    have hinv : ∀ s ∈ S, ∀ v ∈ W, s v ∈ W := by
      intro s hs v hv
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨u, rfl⟩
        simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
        have : s (cfc f A u) = cfc f A (s u) := by
          have := congrArg (fun T : V →L[ℂ] V => T u) (hPcomm s hs).eq
          simpa using this.symm
        rw [this]
        exact Submodule.le_topologicalClosure _ ⟨s u, rfl⟩
      have hcl : IsClosed ((W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) : Submodule ℂ V) : Set V) :=
        (Submodule.isClosed_topologicalClosure _).preimage s.continuous
      exact Submodule.topologicalClosure_minimal _ hle hcl hv
    rcases hirr W (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
    · apply hP0
      ext v
      have : cfc f A v ∈ W := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    · apply hQ0
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨v, rfl⟩
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        have := congrArg (fun T : V →L[ℂ] V => T v) hQP
        simpa using this
      have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
      rw [← hW, htop] at hcl
      ext v
      have : v ∈ LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := hcl Submodule.mem_top
      simpa using this
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

end Schur

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

@[simp] theorem coe_compr_apply (j : ℤ) (g : FiltrationCocycleLiftCriterion) (v : weightSpace σ j) :
    ((compr σ j g v : weightSpace σ j) : H) = wProj σ j (σ g v) := rfl

end GroundTheory.Automorphic.ArchWhittaker
