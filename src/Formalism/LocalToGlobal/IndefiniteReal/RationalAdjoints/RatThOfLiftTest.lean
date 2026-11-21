import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat

section
open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

theorem solve_spec {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) (e : E)
    (he : e ∈ LinearMap.range f) : f (solve f e) = e := by
  have hex : ∃ y, f y = e := he
  unfold solve
  rw [dif_pos hex]
  exact hex.choose_spec

theorem lin_single {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (k : Fin n) :
    lin v (Pi.single k 1) = v k := by
  simp [lin, Fintype.linearCombination_apply_single]

theorem ratMuOfRowTest : RatMuOfRowTest := by
  intro K _ _ _ Bs A X fc cr b hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall, -⟩ := hH2
  intro t i k
  have hmem : X.iC cr b t (Pi.single k 1) ∈ LinearMap.range (X.iC cr b Bs.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat Bs.v0.embedding ψ hψ (X.iC cr b Bs.μ0) hinj0
    (fun j l => by rw [CxData.iC, lin_single]; exact hr _ _ _)
    (solve (X.iC cr b Bs.μ0) (X.iC cr b t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, by simpa [CxData.rowMatC, relMat] using ha⟩

end Formalism.IndefR.Rat
end
end

section
open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

theorem lin_injective {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    Function.Injective (lin v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h := Fintype.linearIndependent_iff.mp hv x
  simp only [lin, Fintype.linearCombination_apply] at hx
  funext i
  exact h hx i

theorem ratThOfLiftTest : RatThOfLiftTest := by
  intro K _ _ _ Bs A X fc cr b hT hH5 hKF hEW hnP j t i k
  obtain ⟨N, ψ, hψ, hr, hbase⟩ := hT j
  have hinjW : Function.Injective (X.eW b j) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := hEW j x x
    rw [hx, inner_zero_left] at h
    have hn : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnP.ne'
    have h2 : ⟪x, x⟫_ℂ = 0 := by
      rcases mul_eq_zero.mp h.symm with h3 | h3
      · exact absurd h3 hn
      · exact h3
    exact inner_self_eq_zero.mp h2
  have hinj : Function.Injective (X.w0C b j) := by
    simp only [CxData.w0C, LinearMap.coe_comp]
    exact hinjW.comp (lin_injective _ (hKF j Bs.v0).1)
  have hmem : X.tC cr b j t (Pi.single k 1) ∈ LinearMap.range (X.w0C b j) := by
    rw [← (hH5 j t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat Bs.v0.embedding ψ hψ (X.w0C b j) hinj (fun i l => hbase i l)
    (solve (X.w0C b j) (X.tC cr b j t (Pi.single k 1)))
    (fun i' => by rw [solve_spec _ _ hmem, CxData.tC, lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, by simpa [CxData.liftMatC, relMat] using ha⟩

end Formalism.IndefR.Rat
end
end
