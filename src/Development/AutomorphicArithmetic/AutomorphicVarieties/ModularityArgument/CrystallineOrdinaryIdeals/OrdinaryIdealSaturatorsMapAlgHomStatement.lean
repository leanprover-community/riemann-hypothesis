import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocNat

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
  {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C)

theorem push_mat (g : GQ l) : (push f r g).mat = (r g).mat.map f := by
  show (GG.map (f : C →+* C') (r g)).mat = _
  rw [GG.map_mat]; rfl

theorem sh_push (a : Fin 3) (s : GQ l) : GlobalTheory.OrdLoc.sh D (push f r) a s = (GlobalTheory.OrdLoc.sh D r a s).map f := by
  unfold GlobalTheory.OrdLoc.sh
  rw [push_mat]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

theorem tr_push (a : Fin 3) : f (GlobalTheory.OrdLoc.tr D r a) = GlobalTheory.OrdLoc.tr D (push f r) a := by
  unfold GlobalTheory.OrdLoc.tr
  rw [sh_push, sh_push, push_mat, ← Matrix.map_mul, ← Matrix.map_mul]
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem dd_push (a : Fin 3) : f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a := by
  unfold GlobalTheory.OrdLoc.dd
  simp only [map_sub, map_mul, AlgHom.commutes, tr_push]

theorem del_push : f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  unfold GlobalTheory.OrdLoc.del
  simp only [map_mul, map_natCast, dd_push]

theorem ordIdeal_push : (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) := by
  unfold GlobalTheory.OrdLoc.ordIdeal
  rw [Ideal.map_span, Set.image_union]
  congr 2
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
      refine ⟨s, hs, i, ?_⟩
      rw [push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]
      rw [← Polynomial.coeff_map]
      simp [Polynomial.map_sub, Polynomial.map_prod]
    · rintro ⟨s, hs, i, rfl⟩
      refine ⟨_, ⟨s, hs, i, rfl⟩, ?_⟩
      rw [push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]
      rw [← Polynomial.coeff_map]
      simp [Polynomial.map_sub, Polynomial.map_prod]
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
      refine ⟨s, hs, i, j, ?_⟩
      rw [sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl
    · rintro ⟨s, hs, i, j, rfl⟩
      refine ⟨_, ⟨s, hs, i, j, rfl⟩, ?_⟩
      rw [sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) :=
  by intro l _ O _ _ _ D C C' _ _ _ _ f r; exact ⟨GlobalTheory.OrdLocNat.ordIdeal_push D f r, GlobalTheory.OrdLocNat.dd_push D f r, GlobalTheory.OrdLocNat.del_push D f r⟩

end GlobalTheory.OrdLocNat
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem push_mat_eq_mat_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : GQ l) : (push f r s).mat = (r s).mat.map f := by
  rfl
private theorem sh_push_eq_sh_map {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) (s : GQ l) : D.sh (push f r) a s = (D.sh r a s).map f := by
  ext i j
  simp only [Dat3.sh, Matrix.sub_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, push_mat_eq_mat_map, map_sub]
  split_ifs <;> simp
private theorem tr_push_algHom_eq_map_tr {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) : D.tr (push f r) a = f (D.tr r a) := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [Dat3.tr, sh_push_eq_sh_map, push_mat_eq_mat_map, h, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
private theorem map_dd_eq_dd_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (a : Fin 3) : f (D.dd r a) = D.dd (push f r) a := by
  simp only [Dat3.dd, tr_push_algHom_eq_map_tr, map_sub, map_mul, AlgHom.commutes]
private theorem map_coeff_charpoly_sub_prod_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : GQ l) (i : ℕ) : f (((r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) = (((push f r s).mat.charpoly - ∏ a, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i) := by
  have h1 : (push f r s).mat.charpoly = (r s).mat.charpoly.map (f : C →+* C') := by
    rw [push_mat_eq_mat_map]
    exact Matrix.charpoly_map _ _
  have h2 : ∀ a : Fin 3, (X - Polynomial.C ((algebraMap O C') (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))) = (X - Polynomial.C ((algebraMap O C) (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))).map (f : C →+* C') := by
    intro a
    simp
  rw [h1, Finset.prod_congr rfl (fun a _ => h2 a), ← Polynomial.map_prod, ← Polynomial.map_sub, Polynomial.coeff_map]
  rfl
private theorem map_sh_triple_prod_apply_eq_push {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C) (s : Fin 3 → GQ l) (i j : Fin 3) : f ((D.sh r 0 (s 0) * D.sh r 1 (s 1) * D.sh r 2 (s 2)) i j) = (D.sh (push f r) 0 (s 0) * D.sh (push f r) 1 (s 1) * D.sh (push f r) 2 (s 2)) i j := by
  have h : ∀ M N : Matrix (Fin 3) (Fin 3) C, M.map f * N.map f = (M * N).map f :=
    fun M N => (Matrix.map_mul (f := (f : C →+* C'))).symm
  simp only [sh_push_eq_sh_map, h, Matrix.map_apply]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryIdeal_saturators_map_algHom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  intro l _ O _ _ _ D C C' _ _ _ _ f r
  refine ⟨?_, fun a => map_dd_eq_dd_push D f r a, ?_⟩
  · simp only [Dat3.ordIdeal]
    rw [Ideal.map_span, Set.image_union]
    congr 2
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
        exact ⟨s, hs, i, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
      · rintro ⟨s, hs, i, rfl⟩
        exact ⟨_, ⟨s, hs, i, rfl⟩, map_coeff_charpoly_sub_prod_eq_push D f r s i⟩
    · ext x
      constructor
      · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
        exact ⟨s, hs, i, j, map_sh_triple_prod_apply_eq_push D f r s i j⟩
      · rintro ⟨s, hs, i, j, rfl⟩
        exact ⟨_, ⟨s, hs, i, j, rfl⟩, map_sh_triple_prod_apply_eq_push D f r s i j⟩
  · simp only [Dat3.del, map_mul, map_natCast, map_dd_eq_dd_push]
end
