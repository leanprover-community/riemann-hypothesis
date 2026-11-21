import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
import BuildAid.ForwardExisting

section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_inf_conj_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.CompanionTheory.Casselman
end

section
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_coset_reps_of_isDom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G,
      (∀ i, x i ∈ D.J ⊓ D.N) ∧
        ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps G D.J
    (D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom) (D.J ⊓ D.N)
    D.isCompact_J (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen G D.J D.isOpen_J (t : G)) inf_le_left inf_le_left
    (exists_mem_inf_conj_of_isDom G D t ht)

end GlobalTheory.CompanionTheory.Casselman
end

open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_coset_reps_unipotent : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ D.J ⊓ D.N) ∧ ∀ y ∈ D.J, ∃! i, (x i)⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom
end
