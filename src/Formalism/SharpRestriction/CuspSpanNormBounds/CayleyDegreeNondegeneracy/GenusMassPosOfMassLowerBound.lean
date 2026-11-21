import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count




end Count

section Lat

variable (D : D7)

def SublatticeFGProjectiveRankLe (u : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M : LatticeW D, M ≤ L0X D Λ (lf D F0) →
    Module.Finite (𝓞 D.host.E) M ∧ Module.Projective (𝓞 D.host.E) M ∧ finrank (𝓞 D.host.E) M ≤ D.R.k

def sublatticesAtLevel (M : LatticeW D) (j : ℕ) : Set (LatticeW D) := {M' | M' ≤ M ∧ sublatticeIndex' D M M' = j}

def levelWeight (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((j : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f))


def latticeQuadruples (L0 : LatticeW D) (s : ℕ) (n : Fin 4 → ℕ) : Set (LatticeW D × LatticeW D × LatticeW D × LatticeW D) :=
  {q | q.1 ∈ PrimSubs (D.sp.X 0).hT L0 (D.R.k - s) (n 0) ∧
    q.2 ∈ {t : LatticeW D × LatticeW D × LatticeW D | t.1 ∈ sublatticesAtLevel D q.1 (n 1) ∧
      t.2 ∈ {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D t.1 (n 2) ∧ w.2 ∈ sublatticesAtLevel D t.1 (n 3)}}}



def indexBox (De : ℝ) : Set (Fin 4 → ℕ) := {q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}


end Lat

section Num




end Num

section Main

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)





end Main

section Inv

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem c3sub_dual_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.dual h M) := by
  have hiso : ∀ x y : V, h (γ x) (γ y) = h x y := fun x y => hγ x y
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.dual E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨γ.symm x, ?_, by simp⟩
    intro m hm
    have hm' := hx (γ m) ⟨m, hm, rfl⟩
    simpa [← hiso m (γ.symm x)] using hm'
  · rintro ⟨z, hz, rfl⟩ y ⟨m, hm, rfl⟩
    have hm' := hz m hm
    simpa [hiso] using hm'






end Inv

section Mean

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenusMassPositive (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ : LatV D, IsRowLat D F0 Λ →
    0 < Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0))



end Mean

end Formalism.MainNotions.BridgeLemma₂

end
