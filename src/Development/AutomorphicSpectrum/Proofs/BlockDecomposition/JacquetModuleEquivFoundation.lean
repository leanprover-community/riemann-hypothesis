import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import BuildAid.ForwardExisting

section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ParabolicCompare

theorem unipRad_stdBlocks_eq_unipotentRadical (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    unipRad k (stdBlocks d hd) = GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd) := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GroundTheory.Automorphic.Parabolic.mem_unipotentRadical,
    GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_parab]
  refine and_congr Iff.rfl ⟨fun H i j hij => ?_, fun H a i j => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
    obtain rfl : a = b := by simpa [Zl.JC.blockIdx] using hij
    have := H a i j
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')
  · rw [H _ _ (by simp [Zl.JC.blockIdx])]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')

end GlobalTheory.CompanionTheory.ParabolicCompare
end

section
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetDict

theorem twKer_one_eq_coinvariantsKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) :
    twKer ρ U 1 = Representation.Coinvariants.ker (ρ.comp U.subtype) := by
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨(n, v), by simp⟩
  · rintro ⟨⟨n, v⟩, rfl⟩
    exact ⟨n, v, by simp⟩

theorem jacquet_stdBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  intro k _ _ _ _ N V _ _ π h d hd
  have hPQ := GlobalTheory.CompanionTheory.ParabolicCompare.unipRad_stdBlocks_eq_unipotentRadical k h N d hd
  have hK : twKer π (unipRad k (stdBlocks d hd)) 1 =
      Representation.Coinvariants.ker
        (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)).subtype) := by
    rw [hPQ]
    exact twKer_one_eq_coinvariantsKer π _
  refine ⟨Submodule.quotEquivOfEq _ _ hK, ?_, ?_⟩
  · intro v
    rfl
  · intro g hg x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

end GlobalTheory.CompanionTheory.JacquetDict
end

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_equiv_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.JacquetDict.jacquet_stdBlocks_equiv
end
