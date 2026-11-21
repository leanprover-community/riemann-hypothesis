import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

section
open Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.AlgebraTools.Det.gcomm :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G),
    (∀ (B : Type) [CommRing B] [Algebra A B] (x y : MonoidAlgebra B G), D.D B (1 + x * y) = D.D B (1 + y * x)) ∧
    ∃ I : TwoSidedIdeal (MonoidAlgebra A G), ∀ y, y ∈ I ↔ D.Kills y := by
  intro n A G _ _ D
  refine ⟨fun B _ _ x y => ?_, D.toDet.ker, fun y =>
    (UpperTheory.V.CA.d_ker D.toDet y).1.trans (UpperTheory.V.CA.d_toDet D y).2.2.2⟩
  have h := UpperTheory.V.CA.d_comm D.toDet B (toT A G B x) (toT A G B y)
  change D.D B (ofT A G B _) = D.D B (ofT A G B _) at h
  simpa only [map_add, map_one, map_mul, ofT_toT] using h
end

section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsStar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D → ∀ y, D.Kills y → D.Kills (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n D hP y hy B _ _ h
  letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨-, -, -, -, -, snat⟩ := AlgebraTools.Det.starApi F O R n
  obtain ⟨bmul, b1, badd, -, binv, -⟩ := AlgebraTools.Det.starApi F O B n
  have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) (F.star O R n y)
      = F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y) :=
    (snat B (IsScalarTower.toAlgHom O R B) y).symm
  rw [hm]
  have key : 1 + h * F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y)
      = F.star O B n (1 + MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y * F.star O B n h) := by
    rw [badd, bmul, b1, binv]
  rw [key, hP B, (AlgebraTools.Det.gcomm D).1 B]
  exact hy B (F.star O B n h)
end
