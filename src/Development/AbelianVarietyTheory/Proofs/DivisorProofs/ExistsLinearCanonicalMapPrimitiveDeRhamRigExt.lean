import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPresentationCocycleMemBialgebraSymmetr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c), IsSymCoc d.g → ∀ n, d.coc n ∈ symCocycles R (G.A n) := by
  first | exact @GlobalTheory.PtExt.coc_mem_symCocycles | exact GlobalTheory.PtExt.coc_mem_symCocycles | (intros; apply GlobalTheory.PtExt.coc_mem_symCocycles <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ), pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by
  first | exact @GlobalTheory.PtExt.Dat.pullTwo_res_coc | exact GlobalTheory.PtExt.Dat.pullTwo_res_coc | (intros; apply GlobalTheory.PtExt.Dat.pullTwo_res_coc <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_sub_tower {B : ℕ → Type} [∀ n, AddCommGroup (B n)] (r : ∀ n, B (n + 1) → B n)
    (hr : ∀ n, Function.Surjective (r n)) (a : ∀ n, B n) :
    ∃ h : ∀ n, B n, ∀ n, a n = h n - r n (h (n + 1)) := by
  choose s hs using hr
  refine ⟨fun n ↦ Nat.rec (motive := B) 0 (fun n x ↦ s n (x - a n)) n, fun n ↦ ?_⟩
  simp only [hs, sub_sub_cancel]

theorem nonempty_dat (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) : Nonempty (Dat t c) := by
  obtain ⟨f, hf⟩ := CatCoh.H1.mk_surjective _ c.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R A f (by rw [hf]; exact c.2)
  obtain ⟨h, hh⟩ := exists_sub_tower (B := fun n ↦ G.A n) (fun n ↦ G.res n) (fun n ↦ G.res_surjective n)
    (fun n ↦ fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))
  exact ⟨⟨f, hf, g, hg, h, hh⟩⟩

end GlobalTheory.PtExt
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), Nonempty (Dat t c) := by
  atlas_forward_decl GlobalTheory.PtExt.nonempty_dat
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

section Basic

variable {X : Over (Sp R)} (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (r : R)

theorem fv_add_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (f + f') D D' φ x = fv f D D' φ x + fv f' D D' φ x := rfl

theorem fv_smul_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (r • f) D D' φ x = r • fv f D D' φ x := rfl

theorem cotVal_add_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (f + f') y = cotVal f y + cotVal f' y := by
  unfold cotVal
  simp only [fv_add_apply, map_add, map_sub]
  abel

theorem cotVal_smul_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (r • f) y = r • cotVal f y := by
  unfold cotVal
  simp only [fv_smul_apply, map_smul, map_sub, smul_sub]

end Basic

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} {t : G.TorsionTower A} {c c' : primDR A}

def Dat.sum (d : Dat t c) (d' : Dat t c') : Dat t (c + c') where
  f := d.f + d'.f
  cl := by rw [map_add, d.cl, d'.cl]; rfl
  g := fun D _ _ x y ↦ d.g D x y + d'.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    have h' := d'.add D D' φ x y
    simp only [fv_add_apply, map_add]
    linear_combination h + h'
  h := fun n ↦ d.h n + d'.h n
  res := fun n ↦ by
    have h := d.res n
    have h' := d'.res n
    simp only [fv_add_apply, map_add]
    linear_combination h + h'

def Dat.scale (r : R) (d : Dat t c) : Dat t (r • c) where
  f := r • d.f
  cl := by rw [map_smul, d.cl]; rfl
  g := fun D _ _ x y ↦ r • d.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h, smul_sub, smul_sub]
  h := fun n ↦ r • d.h n
  res := fun n ↦ by
    have h := d.res n
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h]

theorem Dat.coc_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').coc n = d.coc n + d'.coc n := by
  simp only [Dat.coc, Dat.sum, fv_add_apply, map_add]
  abel

theorem Dat.om_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').om n = d.om n + d'.om n := by
  simp only [Dat.om, Dat.sum, cotVal_add_apply, map_add]
  abel

theorem Dat.coc_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).coc n = r • d.coc n := by
  simp only [Dat.coc, Dat.scale, fv_smul_apply, map_smul, smul_sub]

theorem Dat.om_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).om n = r • d.om n := by
  simp only [Dat.om, Dat.scale, cotVal_smul_apply, map_smul, smul_sub]

theorem isCan_add_smul (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt), IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧
      ∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x) := by
  constructor
  · rintro c c' _ _ ⟨d, z, w, hz, hw, rfl⟩ ⟨d', z', w', hz', hw', rfl⟩
    refine ⟨d.sum d', z + z', w + w', fun n ↦ ?_, fun n ↦ ?_, (map_add G.rigMk _ _).symm⟩
    · rw [Dat.coc_sum, ← hz, ← hz']; rfl
    · rw [Dat.om_sum, ← hw, ← hw']; rfl
  · rintro r c _ ⟨d, z, w, hz, hw, rfl⟩
    refine ⟨d.scale r, r • z, r • w, fun n ↦ ?_, fun n ↦ ?_, (map_smul G.rigMk r (z, w)).symm⟩
    · rw [Dat.coc_scale, ← hz]; rfl
    · rw [Dat.om_scale, ← hw]; rfl

end GlobalTheory.PtExt
end
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), (∀ (c c' : primDR A) (x x' : G.RigExt), IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧ ∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x) := by
  atlas_forward_decl GlobalTheory.PtExt.isCan_add_smul
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  first | exact @GlobalTheory.PtExt.isSymCoc_of_isAdd | exact GlobalTheory.PtExt.isSymCoc_of_isAdd | (intros; apply GlobalTheory.PtExt.isSymCoc_of_isAdd <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A), IsAbelianScheme A → ∀ x x' : G.RigExt, IsCan t c x → IsCan t c x' → x = x' := by
  first | exact @GlobalTheory.PtExt.isCan_unique | exact GlobalTheory.PtExt.isCan_unique | (intros; apply GlobalTheory.PtExt.isCan_unique <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CanMap

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def ext (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) : G.RigExt :=
  G.rigMk (⟨d.coc, fun n ↦ ⟨GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles R A p G t c d hs n, GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq R A p G t c d n⟩⟩,
    ⟨d.om, fun n ↦ GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification R A p G t c d n⟩)

theorem ext_isCan (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) :
    IsCan t c (ext t c d hs) :=
  ⟨d, _, _, fun _ ↦ rfl, fun _ ↦ rfl, rfl⟩

theorem exists_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : ∃ x, IsCan t c x := by
  obtain ⟨d⟩ := GlobalTheory.T.nonempty_primitiveDeRhamTorsionTowerPresentation R A p G t c
  exact ⟨_, ext_isCan t c d (GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor R A hA (fv d.f) d.g d.add)⟩

def canFun (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : G.RigExt :=
  (exists_isCan t hA c).choose

theorem canFun_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) :
    IsCan t c (canFun t hA c) :=
  (exists_isCan t hA c).choose_spec

theorem isCan_iff (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) (x : G.RigExt) :
    IsCan t c x ↔ canFun t hA c = x :=
  ⟨fun h ↦ GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique R A p G t c hA _ _ (canFun_isCan t hA c) h, fun h ↦ h ▸ canFun_isCan t hA c⟩

def canMap (t : G.TorsionTower A) (hA : IsAbelianScheme A) : primDR A →ₗ[R] G.RigExt where
  toFun := canFun t hA
  map_add' c c' := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).1 c c' _ _ (canFun_isCan t hA c) (canFun_isCan t hA c'))
  map_smul' r c := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).2 r c _ (canFun_isCan t hA c))

end GlobalTheory.PtExt.CanMap

theorem GlobalTheory.PtExt.exists_canMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A), IsAbelianScheme A → ∃ L : primDR A →ₗ[R] G.RigExt, ∀ c x, IsCan t c x ↔ L c = x :=
  fun _ _ _ _ _ _ t hA ↦ ⟨GlobalTheory.PtExt.CanMap.canMap t hA, GlobalTheory.PtExt.CanMap.isCan_iff t hA⟩
end
end
