import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSymmRelabel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR

universe u v w

theorem intNum_comp_perm {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n)) :
    intNum F P (bs ∘ σ) = intNum F P bs := by
  unfold intNum
  rw [FieldNumbers.mixedDiff_comp_perm]

theorem SymmStatement.of_type (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] : SymmStatement F ι := by
  classical
  intro I hI V n L σ hV
  have hA : ∀ L' : Fin n → K → ℤ, I V n L' = intNum F V L' := fun L' =>
    Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI V n L' hV
  rw [hA (L ∘ σ), hA L]
  exact intNum_comp_perm V L σ

theorem SymmStatement.of_found (hR : SymmRelabel.Statement.{u, v, w, 0, 0}) {K : Type v}
    [Fintype K] (F : Type u) [Field F] (ι : K → Type w) [∀ k, Fintype (ι k)] :
    SymmStatement F ι := by
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  refine hR F K ι (Fin (Fintype.card K)) (fun j => Fin (Fintype.card (ι (e.symm j)))) e
    (fun k => (Fintype.equivFin (ι k)).trans (finCongr ?_)) (SymmStatement.of_type F _)
  exact congrArg (fun x => Fintype.card (ι x)) (e.symm_apply_apply k).symm

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w v' w'

theorem SymmRelabel.proof : SymmRelabel.Statement.{u, v, w, v', w'} := by
  intro F _ K _ ι _ K' _ ι' _ e h hS I hI V n L σ hV
  have key := hS _ (Relabel.isFieldIntersection_pull e h hI) (V.map (Relabel.ringEquiv F e h)) n
    (fun j => L j ∘ e.symm) σ ((Relabel.isProjVarF_map_iff e h V n).2 hV)
  have hL : ∀ L₀ : Fin n → K → ℤ, (fun j => (fun j => L₀ j ∘ e.symm) j ∘ e) = L₀ := fun L₀ => by
    funext j k
    simp
  simp only [Relabel.pullFamily, Relabel.comap_map] at key
  have h1 := hL (L ∘ σ)
  have h2 := hL L
  simp only [Function.comp_apply] at h1 h2 key
  rw [h1, h2] at key
  exact key

theorem SymmStatement.full {K : Type v} [Fintype K] (F : Type u) [Field F] (ι : K → Type w)
    [∀ k, Fintype (ι k)] : SymmStatement F ι :=
  SymmStatement.of_found SymmRelabel.proof F ι

end GroundTheory.Heights₂.Heights.Targets
end
