import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GramIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi

section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrOpen :
    ∀ {A G ι : Type} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι] (t : G → A),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] (φ : A →+* K) (ρ : G →* Matrix ι ι K) (p : PrimeSpectrum A), p.asIdeal = RingHom.ker φ →
        (∀ g, (ρ g).trace = φ (t g)) → (p ∈ U ↔ Submodule.span K (Set.range ρ) = ⊤) := by
  intro A G ι _ _ _ _ t
  refine ⟨⋃ g : ι × ι → G,
      ((PrimeSpectrum.basicOpen (Matrix.of fun a b => t (g a * g b)).det : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)),
    isOpen_iUnion (fun g => (PrimeSpectrum.basicOpen _).isOpen), ?_⟩
  intro K _ φ ρ p hp htr
  rw [UpperTheory.V.AlgebraTools.Det.gramIff, Set.mem_iUnion]
  apply exists_congr
  intro g
  have hM : φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) =
      Matrix.of fun a b => (ρ (g a * g b)).trace := by
    ext a b
    show φ (t (g a * g b)) = (ρ (g a * g b)).trace
    rw [htr]
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp, RingHom.mem_ker, RingHom.map_det, hM]
end

section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
end

section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.irrOpenDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (p : PrimeSpectrum A),
        p.asIdeal = RingHom.ker φ → D.map φ = GDet.ofRep ρ → (p ∈ U ↔ U3.MatIrr H ρ) := by
  intro n A G _ _ D H
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    intro K _ _ φ ρ p _ _
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  · obtain ⟨U, hU, h⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
      (fun h : H => D.tr (MonoidAlgebra.single (h : G) 1))
    refine ⟨U, hU, ?_⟩
    intro K _ _ φ ρ p hp hD
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    refine h K φ (ρ.comp H.subtype) p hp ?_
    intro g
    have h1 := (UpperTheory.V.AlgebraTools.Det.mapApi D φ).2.2.1 1 (g : G)
    have h2 := (UpperTheory.V.AlgebraTools.Det.repApi ρ).2.2.1 hn (MonoidAlgebra.single (g : G) 1)
    have h3 : GDet.repAlg ρ K (MonoidAlgebra.single (g : G) 1) = ρ g := by
      ext i j; simp [GDet.repAlg]
    rw [hD] at h1
    rw [h3] at h2
    change (ρ g).trace = φ (D.lam 1 _)
    rw [← h1, ← h2]
    rfl
end
