import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInvProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxCompactTransposeInvWeyl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTransformProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseLocal

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.TiArch

open scoped ContDiff

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def tr (A : ArchMatrix K n) : ArchMatrix K n :=
  Matrix.transpose (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from A)

theorem tr_mul (A B : ArchMatrix K n) : tr (A * B) = tr B * tr A :=
  Matrix.transpose_mul (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from A)
    (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from B)

theorem tr_one : tr (1 : ArchMatrix K n) = 1 :=
  Matrix.transpose_one

theorem tr_neg (A : ArchMatrix K n) : tr (-A) = -tr A :=
  Matrix.transpose_neg _

theorem tr_add (A B : ArchMatrix K n) : tr (A + B) = tr A + tr B :=
  Matrix.transpose_add _ _

theorem tr_smul (r : ℝ) (A : ArchMatrix K n) : tr (r • A) = r • tr A :=
  Matrix.transpose_smul _ _

theorem tr_exp (Y : ArchMatrix K n) : NormedSpace.exp (tr Y) = tr (NormedSpace.exp Y) :=
  Matrix.exp_transpose _

def tiA (x : archGroup K n) : archGroup K n :=
  ⟨⟨tr (((x : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n),
    tr ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n),
    by rw [← tr_mul, Units.mul_inv, tr_one],
    by rw [← tr_mul, Units.inv_mul, tr_one]⟩, trivial⟩

theorem coe_tiA (x : archGroup K n) :
    (((tiA x : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
      tr (((x : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) := rfl

theorem tiA_mul (x y : archGroup K n) : tiA (x * y) = tiA x * tiA y := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tiA, _root_.mul_inv_rev, tr_mul]

def dtiA : archLie K n →ₗ[ℝ] archLie K n where
  toFun Y := ⟨-tr (Y : ArchMatrix K n), trivial⟩
  map_add' X Y := by
    apply Subtype.ext
    show -tr ((X : ArchMatrix K n) + (Y : ArchMatrix K n)) = -tr (X : ArchMatrix K n) + -tr (Y : ArchMatrix K n)
    rw [tr_add, neg_add]
  map_smul' r Y := by
    apply Subtype.ext
    show -tr (r • (Y : ArchMatrix K n)) = r • -tr (Y : ArchMatrix K n)
    rw [tr_smul, smul_neg]

theorem tiA_expG (Y : archLie K n) :
    tiA ((isExpLieAlgebra K n).expG Y) = (isExpLieAlgebra K n).expG (dtiA Y) := by
  apply Subtype.ext
  apply Units.ext
  have h : ((((isExpLieAlgebra K n).expG Y : archGroup K n) : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) =
      (((isExpLieAlgebra K n).expG (-Y) : archGroup K n) : (ArchMatrix K n)ˣ) := by
    rw [IsExpLieAlgebra.expG_neg]; rfl
  rw [coe_tiA, h]
  show tr (NormedSpace.exp (-(Y : ArchMatrix K n))) = NormedSpace.exp (-tr (Y : ArchMatrix K n))
  rw [← tr_exp, tr_neg]

theorem isSmoothFun_comp_tiA {f : archGroup K n → ℂ} (hf : (isExpLieAlgebra K n).IsSmoothFun f) :
    (isExpLieAlgebra K n).IsSmoothFun (fun x => f (tiA x)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g
  haveI : FiniteDimensional ℝ (archLie K n) := FiniteDimensional.finiteDimensional_submodule _
  have hL : ContDiff ℝ (∞) (dtiA (K := K) (n := n)) :=
    (LinearMap.toContinuousLinearMap (dtiA (K := K) (n := n))).contDiff
  have e : (fun Y : archLie K n => f (tiA (g * (isExpLieAlgebra K n).expG Y))) =
      (fun Y : archLie K n => f (tiA g * (isExpLieAlgebra K n).expG Y)) ∘ dtiA := by
    funext Y
    rw [Function.comp_apply, tiA_mul, tiA_expG]
  rw [e]
  exact (hf (tiA g)).comp hL

theorem infEmb_fst (y : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((infEmb K n y) a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)) a b := by
  have h1 : ((infEmb K n y) a b).1 = ((archEquiv K n).symm y) a b := by
    have := congrArg (fun p => (p.1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) a b) (prodEquiv_infEmb y)
    exact this
  rw [h1]
  obtain ⟨z, rfl⟩ := (archEquiv K n).surjective y
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem infEmb_snd (y : archGroup K n) (a b : Fin n) :
    ((infEmb K n y) a b).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) a b :=
  congrArg (fun p => (p.2 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) a b) (prodEquiv_infEmb y)

theorem ti_infEmb (x : archGroup K n) : ti (infEmb K n x) = infEmb K n (tiA x) := by
  apply Units.ext
  ext a b
  change (infEmb K n x)⁻¹.val b a = (infEmb K n (tiA x)) a b
  rw [← map_inv]
  refine Prod.ext ?_ ?_
  · apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [infEmb_fst, infEmb_fst]
    rfl
  · rw [infEmb_snd, infEmb_snd]
    exact congrFun (congrFun (Matrix.transpose_one (n := Fin n) (α := FiniteAdeleRing (𝓞 K) K)) a) b

theorem ti_mul' {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m] (a b : GL m R) :
    ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

theorem isArchSmooth_comp_ti :
    ∀ (F : G3 → ℂ), IsArchSmooth F → ∀ c : G3, IsArchSmooth (fun g : G3 => F (c * ti g)) := by
  intro F hF c g
  have e : archSlice (fun g : G3 => F (c * ti g)) g = fun x => archSlice F (c * ti g) (tiA x) := by
    funext x
    simp only [archSlice_apply, ti_mul', ti_infEmb, mul_assoc]
  rw [e]
  exact isSmoothFun_comp_tiA (hF _)

end GlobalTheory.CompanionTheory.TiArch
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archSmooth_comp_transposeInv : ∀ (F : G3 → ℂ), IsArchSmooth F → ∀ c : G3, IsArchSmooth (fun g : G3 => F (c * ti g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TiArch.isArchSmooth_comp_ti
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv

abbrev archT (Y : ArchMatrix ℚ 3) : ArchMatrix ℚ 3 :=
  Matrix.transpose (show Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ) from Y)

theorem exp_archT (Y : ArchMatrix ℚ 3) : NormedSpace.exp (archT Y) = archT (NormedSpace.exp Y) :=
  Matrix.exp_transpose _

theorem ti_mul' (a b : G3) : ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

theorem prodEquiv_ti (g : G3) : AdelicGLn.prodEquiv ℚ 3 (ti g) =
    (ti (AdelicGLn.prodEquiv ℚ 3 g).1, ti (AdelicGLn.prodEquiv ℚ 3 g).2) := by
  have e : (AdelicGLn.prodEquiv ℚ 3 g)⁻¹ = AdelicGLn.prodEquiv ℚ 3 g⁻¹ := (map_inv _ _).symm
  have e1 : ((AdelicGLn.prodEquiv ℚ 3 g).1)⁻¹ = (AdelicGLn.prodEquiv ℚ 3 g⁻¹).1 := congrArg Prod.fst e
  have e2 : ((AdelicGLn.prodEquiv ℚ 3 g).2)⁻¹ = (AdelicGLn.prodEquiv ℚ 3 g⁻¹).2 := congrArg Prod.snd e
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    change (Units.val (g⁻¹ : G3) b a).1 = Units.val ((AdelicGLn.prodEquiv ℚ 3 g).1)⁻¹ b a
    rw [e1]; rfl
  · refine Matrix.ext fun a b => ?_
    change (Units.val (g⁻¹ : G3) b a).2 = Units.val ((AdelicGLn.prodEquiv ℚ 3 g).2)⁻¹ b a
    rw [e2]; rfl

theorem ti_infEmb (x y : archGroup ℚ 3)
    (hxy : ((y : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) =
      archT (((x⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3)) :
    ti (infEmb ℚ 3 x) = infEmb ℚ 3 y := by
  apply (AdelicGLn.prodEquiv ℚ 3).injective
  rw [prodEquiv_ti, prodEquiv_infEmb, prodEquiv_infEmb]
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    change Units.val ((archEquiv ℚ 3).symm x)⁻¹ b a = Units.val ((archEquiv ℚ 3).symm y) a b
    rw [← map_inv]
    change (archMatrixEquiv ℚ 3).symm (((x⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) b a =
      (archMatrixEquiv ℚ 3).symm ((y : (ArchMatrix ℚ 3)ˣ) : ArchMatrix ℚ 3) a b
    rw [hxy]; rfl
  · refine Matrix.ext fun a b => ?_
    change Units.val (1 : AdelicGLn.FiniteAdelicGL ℚ 3)⁻¹ b a = Units.val (1 : AdelicGLn.FiniteAdelicGL ℚ 3) a b
    rw [inv_one]
    exact congrFun (congrFun (Matrix.transpose_one (n := Fin 3) (α := FiniteAdeleRing (𝓞 ℚ) ℚ)) a) b

theorem ti_infEmb_expG (Y Z : archLie ℚ 3)
    (hZ : (Z : ArchMatrix ℚ 3) = archT (-(Y : ArchMatrix ℚ 3))) :
    ti (infEmb ℚ 3 ((isExpLieAlgebra ℚ 3).expG Y)) = infEmb ℚ 3 ((isExpLieAlgebra ℚ 3).expG Z) := by
  apply ti_infEmb
  have e : ((((isExpLieAlgebra ℚ 3).expG Y)⁻¹ : archGroup ℚ 3) : (ArchMatrix ℚ 3)ˣ).val =
      NormedSpace.exp (-(Y : ArchMatrix ℚ 3)) := coe_expUnit_inv ℝ (ArchMatrix ℚ 3) _
  rw [e, IsExpLieAlgebra.coe_expG, hZ, exp_archT]

def eL (i j : Fin 3) : archLie ℚ 3 :=
  ⟨(Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)), Submodule.mem_top⟩

theorem eL_smul (i j : Fin 3) (t : ℝ) :
    (((-t) • eL j i : archLie ℚ 3) : ArchMatrix ℚ 3) = archT (-((t • eL i j : archLie ℚ 3) : ArchMatrix ℚ 3)) := by
  change (-t) • (Matrix.single j i 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ)) =
    Matrix.transpose (-(t • (Matrix.single i j 1 : Matrix (Fin 3) (Fin 3) (mixedEmbedding.mixedSpace ℚ))))
  rw [Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_single, neg_smul]

theorem EA_comp_ti : ∀ (F : archSmooth ℚ 3) (c : G3) (i j : Fin 3) (h : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (c * ti g))),
    ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
      fun g : G3 => -((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) := by
  intro F c i j h
  funext g
  have h1 := (isExpLieAlgebra ℚ 3).hasDerivAt_rightDeriv (h g) (eL i j) 1
  have h2 := (isExpLieAlgebra ℚ 3).hasDerivAt_rightDeriv (F.2 (c * ti g)) (eL j i) 1
  have h2' : HasDerivAt (fun t : ℝ => archSlice (F : G3 → ℂ) (c * ti g) (1 * (isExpLieAlgebra ℚ 3).expG (t • eL j i)))
      ((isExpLieAlgebra ℚ 3).rightDeriv (eL j i) (archSlice (F : G3 → ℂ) (c * ti g)) 1) (-(0 : ℝ)) := by
    simpa using h2
  have h3 := h2'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hfun : (fun t : ℝ => archSlice (fun g : G3 => (F : G3 → ℂ) (c * ti g)) g (1 * (isExpLieAlgebra ℚ 3).expG (t • eL i j))) =
      (fun t : ℝ => archSlice (F : G3 → ℂ) (c * ti g) (1 * (isExpLieAlgebra ℚ 3).expG (t • eL j i))) ∘ Neg.neg := by
    funext t
    simp only [one_mul, archSlice_apply, Function.comp]
    rw [ti_mul', ti_infEmb_expG _ _ (eL_smul i j t), mul_assoc]
  rw [hfun] at h1
  have h4 := h1.unique h3
  have eL1 : ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) g =
      (isExpLieAlgebra ℚ 3).rightDeriv (eL i j) (archSlice (fun g : G3 => (F : G3 → ℂ) (c * ti g)) g) 1 :=
    uAction_ι_apply _ _ g
  have eL2 : ((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) =
      (isExpLieAlgebra ℚ 3).rightDeriv (eL j i) (archSlice (F : G3 → ℂ) (c * ti g)) 1 :=
    uAction_ι_apply _ _ _
  rw [eL1, eL2, h4]
  simp

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv

end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_action_comp_transposeInv : ∀ (F : archSmooth ℚ 3) (c : G3) (i j : Fin 3) (h : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (c * ti g))),
  ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
    fun g : G3 => -((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv.EA_comp_ti
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel

def tiHom : AdelicGLn.FiniteAdelicGL ℚ 3 →* AdelicGLn.FiniteAdelicGL ℚ 3 where
  toFun := ti
  map_one' := by
    apply Units.ext
    change ((1 : AdelicGLn.FiniteAdelicGL ℚ 3)⁻¹ : AdelicGLn.FiniteAdelicGL ℚ 3).val.transpose = 1
    simp
  map_mul' a b := by
    apply Units.ext
    change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
    rw [Matrix.transpose_mul]

theorem continuous_tiHom : Continuous tiHom := by
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_id.matrix_transpose).comp Units.continuous_coe_inv
  · exact (continuous_id.matrix_transpose).comp Units.continuous_val

theorem ti_mul_adelic (a b : G3) : ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

theorem ti_one' {R : Type*} [CommRing R] : ti (1 : GL (Fin 3) R) = 1 := by
  apply Units.ext
  change ((1 : GL (Fin 3) R)⁻¹ : GL (Fin 3) R).val.transpose = 1
  simp

theorem prodEquiv_ti (x : G3) :
    AdelicGLn.prodEquiv ℚ 3 (ti x) =
      (ti (AdelicGLn.prodEquiv ℚ 3 x).1, ti (AdelicGLn.prodEquiv ℚ 3 x).2) := by
  have h : AdelicGLn.prodEquiv ℚ 3 x⁻¹ = (AdelicGLn.prodEquiv ℚ 3 x)⁻¹ := map_inv _ _
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · refine Matrix.ext fun a b => ?_
    have h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).1 b a = ((x⁻¹ : G3) b a).1 := by rw [← h]; rfl
    exact h1.symm
  · refine Matrix.ext fun a b => ?_
    have h1 : ((AdelicGLn.prodEquiv ℚ 3 x)⁻¹).2 b a = ((x⁻¹ : G3) b a).2 := by rw [← h]; rfl
    exact h1.symm

theorem ti_finEmb (u : AdelicGLn.FiniteAdelicGL ℚ 3) :
    ti (finEmb ℚ 3 u) = finEmb ℚ 3 (ti u) := by
  apply (AdelicGLn.prodEquiv ℚ 3).injective
  rw [prodEquiv_ti, prodEquiv_finEmb, prodEquiv_finEmb, ti_one']

theorem ti_level : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∃ U₁ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3),
    ∀ u ∈ U₁, ∃ u' ∈ U₀, ∀ g : G3, ti (g * finEmb ℚ 3 u) = ti g * finEmb ℚ 3 u' := by
  intro U₀
  refine ⟨U₀.comap tiHom continuous_tiHom, fun u hu => ⟨ti u, hu, fun g => ?_⟩⟩
  rw [ti_mul_adelic, ti_finEmb]

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_subgroup_transposeInv_compat : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∃ U₁ : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3),
  ∀ u ∈ U₁, ∃ u' ∈ U₀, ∀ g : G3, ti (g * finEmb ℚ 3 u) = ti g * finEmb ℚ 3 u' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.TrLevel.ti_level
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrGauge

theorem ti_dg {R : Type*} [CommRing R] (x y z : Rˣ) :
    ti (dg x y z) = dg x⁻¹ y⁻¹ z⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ti, dg]

theorem dg_mul {R : Type*} [CommRing R] (x y z x' y' z' : Rˣ) :
    dg x y z * dg x' y' z' = dg (x * x') (y * y') (z * z') := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl_mul_diag_GL3 {R : Type*} [CommRing R] (x y z : Rˣ) :
    (w3 : GL (Fin 3) R) * dg x y z = dg z y x * w3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, w3, Matrix.mul_apply, Fin.sum_univ_three]

theorem rational_sign_diag_adelic : dia dl3 = dg 1 (-1) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dl3, dg]

theorem transposeInv_rational_sign : ti (dia dl3) = dg 1 (-1) 1 := by
  rw [rational_sign_diag_adelic, ti_dg]
  simp

theorem c_mul_dg (x y z : (𝔸[ℚ])ˣ) :
    (w3 : G3) * ti (dia dl3) * dg x y z = dg z y x * ((w3 : G3) * ti (dia dl3)) := by
  rw [transposeInv_rational_sign, mul_assoc, dg_mul, longWeyl_mul_diag_GL3, longWeyl_mul_diag_GL3, ← mul_assoc, dg_mul]
  simp

theorem tr_dg_mul (W : G3 → ℂ) (hW : ∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) (a b : (𝔸[ℚ])ˣ) (k : G3) :
    tr W (dg (a * b) b 1 * k) = W (dg (b * a) a 1 * ((w3 : G3) * ti (dia dl3) * ti k)) := by
  have hd : dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹ * dg (b * a) a 1 = dg 1⁻¹ b⁻¹ (a * b)⁻¹ := by
    have e1 : (a * b)⁻¹ * (b * a) = 1⁻¹ := by rw [mul_comm b a, inv_mul_cancel, inv_one]
    have e2 : (a * b)⁻¹ * a = b⁻¹ := by
      rw [mul_inv, mul_comm a⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [dg_mul, e1, e2, mul_one]
  rw [GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main.1 W, ← hW (a * b)⁻¹ (dg (b * a) a 1 * _), (GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg.1 _ _ _ _).1, ti_dg,
    ← mul_assoc (dg (a * b)⁻¹ (a * b)⁻¹ (a * b)⁻¹), hd, ← mul_assoc ((w3 : G3) * ti (dia dl3)), c_mul_dg,
    inv_one, mul_assoc]

theorem c_ti_mem {k : G3} (hk : k ∈ (maxCompact : Subgroup G3)) :
    (w3 : G3) * ti (dia dl3) * ti k ∈ (maxCompact : Subgroup G3) :=
  mul_mem (mul_mem GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.1 (GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.2.2.2.1 _ GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.1))
    (GlobalTheory.CompanionTheory.UnfoldingAlt.TiK.weyl_delta_ti_maxCompact.2.2.2.2.1 _ hk)

theorem tr_gauge : ∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖(tr W) (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      ((tr W) (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) := by
  rintro W hW ⟨Ω, hΩ, T, h⟩
  refine ⟨Ω, hΩ, T, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h N
  refine ⟨C, fun a b k hk w => ?_⟩
  obtain ⟨h1, h2⟩ := hC b a _ (c_ti_mem hk) w
  rw [tr_dg_mul W hW a b k]
  refine ⟨?_, fun hne => (h2 hne).symm⟩
  rw [mul_comm (IdeleGroup.ideleModule ℚ a : ℝ), mul_comm (1 + ‖(a : 𝔸[ℚ]).1 w‖)]
  exact h1

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrGauge
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transposeInv_properties : (∀ (R : Type) [CommRing R] (n : ℕ) (g h : GL (Fin n) R), ti (g * h) = ti g * ti h ∧ ti (ti g) = g) ∧
  (∀ γ : GL (Fin 3) ℚ, ti (dia γ) = dia (ti γ)) ∧ (∀ γ : GL (Fin 2) ℚ, ti (dia2 γ) = dia2 (ti γ)) ∧
  Continuous (ti : G3 → G3) ∧ Continuous (ti : G2 → G2) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg | exact GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_transform_properties : (∀ (W : G3 → ℂ) (g : G3), tr W g = W (w3 * ti (dia dl3) * ti g)) ∧
  (∀ (W : G3 → ℂ) (h g : G3), tr W (g * h) = tr (fun x => W (x * ti h)) g) ∧
  Function.Injective tr ∧
  (∀ W : G3 → ℂ, (∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g) →
    ∀ x y z g, tr W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * tr W g) ∧
  (∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) → ∀ (a : (𝔸[ℚ])ˣ) g, tr W (dg a a a * g) = tr W g) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main | exact GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_GL3_adelic_decay : ∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) → (∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖(tr W) (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      ((tr W) (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.TrGauge.tr_gauge
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV

theorem tr_eq_fun (W : G3 → ℂ) :
    tr W = fun g : G3 => W ((w3 * ti (dia dl3)) * ti g) :=
  funext (GlobalTheory.T.whittaker_transform_properties.1 W)

theorem EA_tr (W : G3 → ℂ) (hW : IsArchSmooth W) (h : IsArchSmooth (tr W)) (i j : Fin 3) :
    ((EA i j ⟨tr W, h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
      tr (-((EA j i ⟨W, hW⟩ : archSmooth ℚ 3) : G3 → ℂ)) := by
  have e := tr_eq_fun W
  have h' : IsArchSmooth (fun g : G3 => W ((w3 * ti (dia dl3)) * ti g)) := e ▸ h
  have key := GlobalTheory.T.lie_action_comp_transposeInv ⟨W, hW⟩ (w3 * ti (dia dl3)) i j h'
  have hs : (⟨tr W, h⟩ : archSmooth ℚ 3) =
      ⟨fun g : G3 => W ((w3 * ti (dia dl3)) * ti g), h'⟩ := Subtype.ext e
  rw [hs]
  refine key.trans ?_
  rw [tr_eq_fun]
  rfl

theorem whA_tV : ∀ V : Submodule ℂ (G3 → ℂ), WhA V → WhA (tV V) := by
  intro V hV
  have mem : ∀ {W : G3 → ℂ}, W ∈ V → tr W ∈ tV V := fun hW =>
    Submodule.mem_map_of_mem (f := trL) hW
  have arch : ∀ F ∈ tV V, IsArchSmooth F := by
    rintro _ ⟨W, hW, rfl⟩
    change IsArchSmooth (tr W)
    rw [tr_eq_fun]
    exact GlobalTheory.T.archSmooth_comp_transposeInv W (hV.arch W hW) _
  refine ⟨?_, ?_, ?_, arch, ?_, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩ h
    have e : (fun g => trL W (g * h)) = tr (fun x => W (x * ti h)) :=
      funext fun g => GlobalTheory.T.whittaker_transform_properties.2.1 W h g
    rw [e]
    exact mem (hV.stable W hW (ti h))
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_transform_properties.2.2.2.1 W (hV.psi W hW)
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_transform_properties.2.2.2.2 W (hV.cen W hW)
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨U₀, hU₀⟩ := hV.level W hW
    obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.open_subgroup_transposeInv_compat U₀
    refine ⟨U₁, fun g u hu => ?_⟩
    obtain ⟨u', hu', hti⟩ := hU₁ u hu
    change tr W (g * finEmb ℚ 3 u) = tr W g
    rw [GlobalTheory.T.whittaker_transform_properties.1 W, GlobalTheory.T.whittaker_transform_properties.1 W, hti, ← mul_assoc]
    exact hU₀ _ u' hu'
  · rintro _ ⟨W, hW, rfl⟩ i j
    have h : IsArchSmooth (tr W) := arch _ (mem hW)
    change ((EA i j ⟨tr W, h⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ tV V
    rw [EA_tr W (hV.arch W hW) h i j]
    exact mem (V.neg_mem (hV.lie W hW j i))
  · rintro _ ⟨W, hW, rfl⟩
    exact GlobalTheory.T.whittaker_GL3_adelic_decay W (hV.cen W hW) (hV.gauge W hW)

end GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_space_transpose_inverse : ∀ V : Submodule ℂ (G3 → ℂ), WhA V → WhA (tV V) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.WhatV.whA_tV
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt

theorem locHeight_ti {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) :
    locHeight (ti g) = locHeight g := by
  have hv : ∀ i j, ((ti g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) j i := fun _ _ => rfl
  have hi : ∀ i j, (((ti g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      (g : Matrix (Fin n) (Fin n) E) j i := fun _ _ => rfl
  refine le_antisymm (locHeight_le (one_le_locHeight g) (fun i j => ?_) fun i j => ?_)
    (locHeight_le (one_le_locHeight _) (fun i j => ?_) fun i j => ?_)
  · rw [hv]; exact norm_inv_apply_le_locHeight g j i
  · rw [hi]; exact norm_apply_le_locHeight g j i
  · rw [← hi]; exact norm_inv_apply_le_locHeight (ti g) j i
  · rw [← hv]; exact norm_apply_le_locHeight (ti g) j i

theorem infAt_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (w : InfinitePlace K)
    (g : AdelicGLn.AdelicGL K n) : infAt w (ti g) = ti (infAt w g) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) b a)).1 w =
    (((infAt w g)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion) b a
  rw [← Reduction.infAt_inv]
  rfl

theorem finAt_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : AdelicGLn.AdelicGL K n) : finAt v (ti g) = ti (finAt v g) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) b a)).2 v =
    (((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion K)) b a
  rw [← Reduction.finAt_inv]
  rfl

theorem height_ti {K : Type*} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    height (ti g) = height g := by
  simp only [height, infAt_ti, finAt_ti, locHeight_ti]

theorem hasModerateGrowth_comp_ti :
    ∀ φ : G3 → ℂ, HasModerateGrowth φ → HasModerateGrowth (fun g : G3 => φ (ti g)) := by
  rintro φ ⟨C, N, h⟩
  exact ⟨C, N, fun g => by simpa only [height_ti] using h (ti g)⟩

end GlobalTheory.CompanionTheory.UnfoldingAlt

end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_comp_transposeInv : ∀ φ : G3 → ℂ, HasModerateGrowth φ → HasModerateGrowth (fun g : G3 => φ (ti g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.hasModerateGrowth_comp_ti
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.TiCusp

variable {r s : ℕ} {R : Type*} [CommRing R]

def sw (h : r + s = 3) (p : UPos 3 s) : UPos 3 r :=
  ⟨(Fin.rev p.1.2, Fin.rev p.1.1), by
    have h1 := p.2.1
    have h2 := p.2.2
    have h3 := p.1.1.2
    have h4 := p.1.2.2
    simp only [Fin.val_rev]
    omega⟩

theorem sw_sw (h : r + s = 3) (h' : s + r = 3) (p : UPos 3 s) : sw h' (sw h p) = p := by
  apply Subtype.ext
  simp [sw]

def swE (h : r + s = 3) : UPos 3 s ≃ UPos 3 r :=
  ⟨sw h, sw (by omega), sw_sw h _, sw_sw _ h⟩

def tX (h : r + s = 3) (X : UPos 3 r → R) : UPos 3 s → R := fun p => -X (sw h p)

theorem tX_tX (h : r + s = 3) (h' : s + r = 3) (X : UPos 3 r → R) : tX h' (tX h X) = X := by
  funext p
  simp [tX, sw_sw]

theorem tX_add (h : r + s = 3) (X Y : UPos 3 r → R) : tX h (X + Y) = tX h X + tX h Y := by
  funext p
  simp [tX, add_comm]

theorem longWeyl_mul_apply (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (((w3 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * M) i j = M (Fin.rev i) j := by
  fin_cases i <;> simp [w3, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

theorem mul_longWeyl_apply (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (M * ((w3 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i j = M i (Fin.rev j) := by
  fin_cases j <;> simp [w3, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

theorem longWeyl_transposeInv_unipotent (h : r + s = 3) (X : UPos 3 r → R) :
    w3 * ti (unipGL X) = unipGL (tX h X) * w3 := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, longWeyl_mul_apply, mul_longWeyl_apply]
  change ((unipGL X)⁻¹ : GL (Fin 3) R).val j (Fin.rev i) = (unipMatrix (tX h X)) i (Fin.rev j)
  rw [coe_unipGL_inv]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  have e1 : (j = Fin.rev i) ↔ (i = Fin.rev j) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  have e2 : ((j : ℕ) < r ∧ r ≤ (Fin.rev i : ℕ)) ↔ ((i : ℕ) < s ∧ s ≤ (Fin.rev j : ℕ)) := by
    have := i.2
    have := j.2
    simp only [Fin.val_rev]
    omega
  by_cases c : (j : ℕ) < r ∧ r ≤ (Fin.rev i : ℕ)
  · rw [dif_pos c, dif_pos (e2.1 c)]
    simp only [e1, tX, Pi.neg_apply]
    congr 2
    congr 1
    apply Subtype.ext
    simp [sw]
  · rw [dif_neg c, dif_neg (fun d => c (e2.2 d))]
    simp only [e1]

def tE (h : r + s = 3) : (UPos 3 r → 𝔸[ℚ]) ≃ᵐ (UPos 3 s → 𝔸[ℚ]) where
  toFun := tX h
  invFun := tX (by omega)
  left_inv X := tX_tX h _ X
  right_inv X := tX_tX _ h X
  measurable_toFun := measurable_pi_lambda _ fun p => (measurable_pi_apply _).neg
  measurable_invFun := measurable_pi_lambda _ fun p => (measurable_pi_apply _).neg

theorem tE_apply (h : r + s = 3) (X : UPos 3 r → 𝔸[ℚ]) : tE h X = tX h X := rfl

theorem mp_tE (h : r + s = 3) :
    MeasurePreserving (tE h) (unipMeasure ℚ 3 r) (unipMeasure ℚ 3 s) := by
  refine ⟨(tE h).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (tE h).measurable (MeasurableSet.univ_pi hS)]
  have e : (tE h) ⁻¹' (Set.univ.pi S) =
      Set.univ.pi (fun p : UPos 3 r => Neg.neg ⁻¹' S ((swE h).symm p)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, tE_apply]
    constructor
    · intro H p
      have := H ((swE h).symm p)
      have e2 : sw h ((swE h).symm p) = p := (swE h).apply_symm_apply p
      simpa [tX, e2] using this
    · intro H q
      have := H (swE h q)
      simpa [tX, swE, sw_sw] using this
  rw [e, Measure.pi_pi]
  exact Fintype.prod_equiv (swE h).symm _ _ fun p => Measure.measure_preimage_neg _ _

theorem isFD_preimage (h : r + s = 3) :
    IsAddFundamentalDomain (unipLattice ℚ 3 s) ((tE h).symm ⁻¹' unipFundamentalDomain ℚ 3 r)
      (unipMeasure ℚ 3 s) := by
  have h' : s + r = 3 := by omega
  have hmem : ∀ {a b : ℕ} (k : a + b = 3) (ξ : unipLattice ℚ 3 a), tX k ξ.1 ∈ unipLattice ℚ 3 b := by
    rintro a b k ⟨_, ξ, rfl⟩
    refine ⟨tX k ξ, ?_⟩
    funext p
    simp [tX]
  refine isAddFundamentalDomain_unipFundamentalDomain.preimage_of_equiv
    (mp_tE h).symm.quasiMeasurePreserving (e := fun ξ => ⟨tX h ξ.1, hmem h ξ⟩) ?_ ?_
  · constructor
    · intro ξ η e
      have := congrArg (fun z : unipLattice ℚ 3 s => tX h' z.1) e
      simp only [tX_tX] at this
      exact Subtype.ext this
    · intro η
      exact ⟨⟨tX h' η.1, hmem h' η⟩, Subtype.ext (tX_tX h' h η.1)⟩
  · intro ξ Y
    change tX h' (tX h ξ.1 + Y) = ξ.1 + tX h' Y
    rw [tX_add, tX_tX]

theorem diagonal_weyl_GL3 : AdelicGLn.diagonal ℚ 3 w3 = (w3 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AdelicGLn.diagonal_apply, w3]

theorem constantTerm_ti {φ : G3 → ℂ} (hφ : IsLeftInvariant φ) (h : r + s = 3) (g : G3) :
    constantTerm r (fun g : G3 => φ (ti g)) g = constantTerm s φ (w3 * ti g) := by
  rw [constantTerm_eq_setIntegral hφ (isFD_preimage h)]
  rw [← (mp_tE h).setIntegral_preimage_emb (tE h).measurableEmbedding]
  have e : (tE h) ⁻¹' ((tE h).symm ⁻¹' unipFundamentalDomain ℚ 3 r) =
      unipFundamentalDomain ℚ 3 r := by
    ext X
    simp
  rw [e, constantTerm]
  refine setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X _ => ?_
  change φ (ti (unipGL X * g)) = φ (unipGL (tX h X) * (w3 * ti g))
  rw [← mul_assoc, ← longWeyl_transposeInv_unipotent h, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, mul_assoc,
    ← diagonal_weyl_GL3, hφ]

theorem isCuspidal_comp_ti :
    ∀ φ : G3 → ℂ, IsLeftInvariant φ → IsCuspidal φ → IsCuspidal (fun g : G3 => φ (ti g)) := by
  intro φ hφ hc r hr hr3 g
  rw [constantTerm_ti hφ (s := 3 - r) (by omega)]
  exact hc (3 - r) (by omega) (by omega) _

end GlobalTheory.CompanionTheory.TiCusp

end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_comp_transposeInv : ∀ φ : G3 → ℂ, IsLeftInvariant φ → IsCuspidal φ → IsCuspidal (fun g : G3 => φ (ti g)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TiCusp.isCuspidal_comp_ti
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit

open GroundTheory.Automorphic.FourierWhittaker

abbrev pa : Pos 3 := ⟨(0, 1), by decide⟩

abbrev pb : Pos 3 := ⟨(0, 2), by decide⟩

abbrev pc : Pos 3 := ⟨(1, 2), by decide⟩

theorem setIntegral_sub_of_periodic {ι : Type*} [Fintype ι] (F : (ι → 𝔸[ℚ]) → ℂ)
    (hF : ∀ ξ ∈ vecLattice ℚ ι, ∀ x, F (ξ + x) = F x) (c : ι → 𝔸[ℚ]) :
    ∫ y in vecDomain ℚ ι, F (c - y) ∂vecMeasure ℚ ι = ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι := by
  have hD := isAddFundamentalDomain_vecDomain (K := ℚ) (ι := ι)
  let T : (ι → 𝔸[ℚ]) ≃+ (ι → 𝔸[ℚ]) := AddEquiv.neg _
  have hcn : Continuous fun x : ι → 𝔸[ℚ] => -x := continuous_neg
  have h1 := setIntegral_comp_addEquiv T hcn hcn
    (isAddFundamentalDomain_image_of_map_vecLattice T hcn (fun x => by
      change x ∈ vecLattice ℚ ι ↔ -x ∈ vecLattice ℚ ι
      exact (neg_mem_iff).symm))
    (f := fun u => F (c + u)) (fun ξ hξ x => by
      rw [show c + (ξ + x) = ξ + (c + x) by abel]
      exact hF ξ hξ _)
  have h2 : ∫ y in vecDomain ℚ ι, F (c + y) ∂vecMeasure ℚ ι =
      ∫ y in vecDomain ℚ ι, F y ∂vecMeasure ℚ ι := by
    have e1 : ∫ y in vecDomain ℚ ι, F (c + y) ∂vecMeasure ℚ ι =
        ∫ y in (fun y => c + y) '' vecDomain ℚ ι, F y ∂vecMeasure ℚ ι :=
      ((measurePreserving_add_left (vecMeasure ℚ ι) c).setIntegral_image_emb
        (measurableEmbedding_addLeft c) F _).symm
    have e2 : (fun y => c + y) '' vecDomain ℚ ι = c +ᵥ vecDomain ℚ ι := rfl
    rw [e1, e2]
    refine (hD.vadd_of_comm c).setIntegral_eq hD fun l x => ?_
    exact hF l l.2 x
  calc ∫ y in vecDomain ℚ ι, F (c - y) ∂vecMeasure ℚ ι
      = ∫ y in vecDomain ℚ ι, F (c + T y) ∂vecMeasure ℚ ι := by
        refine setIntegral_congr_fun measurableSet_vecDomain fun y _ => ?_
        change F (c - y) = F (c + -y)
        rw [sub_eq_add_neg]
    _ = _ := h1.trans h2

def sp : Pos 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun p := if p = pa then Sum.inl 0 else if p = pc then Sum.inl 1 else Sum.inr 0
  invFun := Sum.elim (fun i => if i = 0 then pa else pc) (fun _ => pb)
  left_inv := by decide
  right_inv := by decide

def sw : Pos 3 ≃ Pos 3 where
  toFun p := if p = pa then pc else if p = pc then pa else p
  invFun p := if p = pa then pc else if p = pc then pa else p
  left_inv := by decide
  right_inv := by decide

def fl (X : Pos 3 → 𝔸[ℚ]) : Pos 3 → 𝔸[ℚ] := fun p => if p = pb then X pa * X pc - X pb else X p

theorem continuous_fl : Continuous fl := by
  refine continuous_pi fun p => ?_
  simp only [fl]
  split_ifs
  · have ha : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pa := continuous_apply pa
    have hb : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pb := continuous_apply pb
    have hc : Continuous fun X : Pos 3 → 𝔸[ℚ] => X pc := continuous_apply pc
    exact (ha.mul hc).sub hb
  · exact continuous_apply _

theorem setIntegral_comp_sw (h : (Pos 3 → 𝔸[ℚ]) → ℂ) :
    ∫ X in vecDomain ℚ (Pos 3), h (fun p => X (sw p)) ∂vecMeasure ℚ (Pos 3) =
      ∫ X in vecDomain ℚ (Pos 3), h X ∂vecMeasure ℚ (Pos 3) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : Pos 3 => 𝔸[ℚ]) sw
  have hE : MeasurePreserving E (vecMeasure ℚ (Pos 3)) (vecMeasure ℚ (Pos 3)) :=
    measurePreserving_piCongrLeft (fun _ : Pos 3 => GroundTheory.Global.adeleMeasure ℚ) sw
  have hsw : ∀ p, sw.symm p = sw p := fun p => rfl
  have hEX : ∀ X : Pos 3 → 𝔸[ℚ], E X = fun p => X (sw p) := by
    intro X
    funext p
    simp [E, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, hsw]
  have hpre : E ⁻¹' vecDomain ℚ (Pos 3) = vecDomain ℚ (Pos 3) := by
    ext X
    simp only [Set.mem_preimage, hEX, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hX p
      have := hX (sw p)
      simpa [hsw, show sw (sw p) = p from sw.left_inv p] using this
    · intro hX p
      exact hX _
  have := hE.setIntegral_preimage_emb E.measurableEmbedding h (vecDomain ℚ (Pos 3))
  rw [hpre] at this
  simpa only [hEX] using this

theorem setIntegral_comp_fl {h : (Pos 3 → 𝔸[ℚ]) → ℂ} (hc : Continuous h)
    (hp : ∀ (r : ℚ) (X : Pos 3 → 𝔸[ℚ]),
      h (fun p => if p = pb then algebraMap ℚ 𝔸[ℚ] r + X p else X p) = h X) :
    ∫ X in vecDomain ℚ (Pos 3), h (fl X) ∂vecMeasure ℚ (Pos 3) =
      ∫ X in vecDomain ℚ (Pos 3), h X ∂vecMeasure ℚ (Pos 3) := by
  rw [setIntegral_vecDomain_sum (h := fun X => h (fl X)) sp (hc.comp continuous_fl),
    setIntegral_vecDomain_sum sp hc]
  refine setIntegral_congr_fun measurableSet_vecDomain fun w _ => ?_
  have key := setIntegral_sub_of_periodic (ι := Fin 1)
    (fun y => h (fun i => Sum.elim w y (sp i))) ?_ (fun _ => w 0 * w 1)
  · rw [← key]
    refine setIntegral_congr_fun measurableSet_vecDomain fun y _ => ?_
    congr 1
    funext p
    have h1 : sp pa = Sum.inl 0 := by decide
    have h2 : sp pc = Sum.inl 1 := by decide
    have h3 : sp pb = Sum.inr 0 := by decide
    by_cases hb : p = pb
    · subst hb
      simp [fl, h1, h2, h3]
    · simp only [fl, if_neg hb]
      rcases hs : sp p with a | b
      · simp
      · exfalso
        apply hb
        have : b = 0 := Subsingleton.elim _ _
        subst this
        exact sp.injective (hs.trans h3.symm)
  · rintro _ ⟨ξ, rfl⟩ y
    rw [← hp (ξ 0) (fun i => Sum.elim w y (sp i))]
    congr 1
    funext p
    have h3 : sp pb = Sum.inr 0 := by decide
    by_cases hb : p = pb
    · subst hb
      simp [h3]
    · simp only [if_neg hb]
      rcases hs : sp p with a | b
      · simp
      · exfalso
        apply hb
        have : b = 0 := Subsingleton.elim _ _
        subst this
        exact sp.injective (hs.trans h3.symm)

theorem supSum_three (X : Pos 3 → 𝔸[ℚ]) : supSum 0 X = X pa + X pc := by
  have h : Finset.univ.filter (fun p : Pos 3 => p.1.2.val = p.1.1.val + 1 ∧ 0 ≤ p.1.2.val) =
      {pa, pc} := by decide
  rw [supSum, h, Finset.sum_pair (by decide)]

theorem uGL_eq_uni {R : Type*} [CommRing R] (X : Pos 3 → R) : uGL X = uni (X pa) (X pb) (X pc) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni, uMat_apply]

theorem ti_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (a b : GL n R) :
    ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

def cq : GL (Fin 3) ℚ := w3 * ti dl3

theorem transposeInv_sign_diag : ti dl3 = dl3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ti, dl3, dg]

theorem ti_dia (γ : GL (Fin 3) ℚ) : ti (dia γ) = dia (ti γ) := by
  apply Units.ext
  ext i j
  simp [dia, ti, AdelicGLn.diagonal]

theorem coe_dia_cq :
    ((dia cq : G3) : Matrix (Fin 3) (Fin 3) 𝔸[ℚ]) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  rw [show cq = w3 * dl3 by rw [cq, transposeInv_sign_diag]]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dl3, dg, w3, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three]

theorem dia_cq : dia cq = w3 * ti (dia dl3) := by
  rw [ti_dia, transposeInv_sign_diag]
  apply Units.ext
  rw [coe_dia_cq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dl3, dg, w3, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_uni (x y z : 𝔸[ℚ]) :
    w3 * ti (dia dl3) * ti (uni x y z) = uni z (z * x - y) x * (w3 * ti (dia dl3)) := by
  rw [← dia_cq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dia_cq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ti, uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem dia_uni_mul (r : ℚ) (x y z : 𝔸[ℚ]) :
    dia (uni (0 : ℚ) r 0) * uni x y z = uni x (algebraMap ℚ 𝔸[ℚ] r + y) z := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni, AdelicGLn.diagonal, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem whittaker_ti : ∀ φ : G3 → ℂ, IsLeftInvariant φ → Continuous φ → ∀ g : G3,
    FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g = tr (FourierWhittaker.whittaker φ) g := by
  intro φ hL hc g
  obtain ⟨g', hg'⟩ : ∃ g' : G3, g' = w3 * ti (dia dl3) * ti g := ⟨_, rfl⟩
  have htr : tr (FourierWhittaker.whittaker φ) g = FourierWhittaker.whittaker φ g' := by
    simp only [tr, dualWhittakerAdelicGL3]
    rw [ti_mul, hg', mul_assoc]
  rw [htr]
  have hcont := continuous_wInt 0 hc g'
  have hpt : ∀ X : Pos 3 → 𝔸[ℚ], φ (ti (uGL X * g)) * (adelicChar ℚ (-supSum 0 X) : ℂ) =
      (fun Y => wInt 0 φ g' (fl Y)) (fun p => X (sw p)) := by
    intro X
    have h1 : sw pa = pc := by decide
    have h2 : sw pc = pa := by decide
    have h3 : sw pb = pb := by decide
    have ea : fl (fun p => X (sw p)) pa = X pc := by simp [fl, h1]
    have eb : fl (fun p => X (sw p)) pb = X pc * X pa - X pb := by simp [fl, h1, h2, h3]
    have ec : fl (fun p => X (sw p)) pc = X pa := by simp [fl, h2]
    simp only [wInt]
    rw [uGL_eq_uni (fl _), supSum_three (fl _), ea, eb, ec, supSum_three X, add_comm (X pc),
      ← hL cq, show AdelicGLn.diagonal ℚ 3 cq = w3 * ti (dia dl3) from dia_cq, ti_mul, ← mul_assoc,
      uGL_eq_uni X, conj_uni, hg', mul_assoc]
  have hper : ∀ (r : ℚ) (X : Pos 3 → 𝔸[ℚ]),
      wInt 0 φ g' (fun p => if p = pb then algebraMap ℚ 𝔸[ℚ] r + X p else X p) = wInt 0 φ g' X := by
    intro r X
    simp only [wInt]
    rw [uGL_eq_uni (fun p => _), supSum_three (fun p => _), uGL_eq_uni X, supSum_three X]
    simp only [if_neg (show pa ≠ pb by decide), if_neg (show pc ≠ pb by decide), if_true]
    rw [← dia_uni_mul, mul_assoc, hL]
  calc FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g
      = ∫ X in vecDomain ℚ (Pos 3), (fun Y => wInt 0 φ g' (fl Y)) (fun p => X (sw p))
          ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_congr_fun measurableSet_vecDomain fun X _ => hpt X
    _ = ∫ X in vecDomain ℚ (Pos 3), wInt 0 φ g' (fl X) ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_comp_sw (fun Y => wInt 0 φ g' (fl Y))
    _ = ∫ X in vecDomain ℚ (Pos 3), wInt 0 φ g' X ∂vecMeasure ℚ (Pos 3) :=
        setIntegral_comp_fl hcont hper
    _ = FourierWhittaker.whittaker φ g' := rfl

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit

end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_comp_transposeInv : ∀ φ : G3 → ℂ, IsLeftInvariant φ → Continuous φ → ∀ g : G3,
  FourierWhittaker.whittaker (fun g : G3 => φ (ti g)) g = tr (FourierWhittaker.whittaker φ) g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.UnfoldingAlt.TiWhit.whittaker_ti
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.LiftTV

theorem arch_ti (F : archSmooth ℚ 3) : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (ti g)) := by
  simpa using GlobalTheory.T.archSmooth_comp_transposeInv F F.2 1

def S : archSmooth ℚ 3 →ₗ[ℂ] archSmooth ℚ 3 where
  toFun F := ⟨fun g => (F : G3 → ℂ) (ti g), arch_ti F⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem S_apply (F : archSmooth ℚ 3) (g : G3) : (S F : G3 → ℂ) g = (F : G3 → ℂ) (ti g) := rfl

theorem ti_mul (g h : G3) : ti (g * h) = ti g * ti h :=
  (GlobalTheory.T.transposeInv_properties.1 _ _ g h).1

theorem tr_eq (W : G3 → ℂ) : tr W = fun g => W (w3 * ti (dia dl3) * ti g) :=
  funext (GlobalTheory.T.whittaker_transform_properties.1 W)

theorem tr_mem {V : Submodule ℂ (G3 → ℂ)} (W : V) : tr W.1 ∈ tV V :=
  Submodule.mem_map.2 ⟨W.1, W.2, rfl⟩

def e (V : Submodule ℂ (G3 → ℂ)) : V ≃ₗ[ℂ] tV V :=
  Submodule.equivMapOfInjective trL GlobalTheory.T.whittaker_transform_properties.2.2.1 V

def U' {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) : tV V →ₗ[ℂ] archSmooth ℚ 3 :=
  S ∘ₗ U ∘ₗ (e V).symm.toLinearMap

theorem U'_e {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) (W : V) :
    U' U (e V W) = S (U W) := by
  simp [U']

theorem U'_tr {V : Submodule ℂ (G3 → ℂ)} (U : V →ₗ[ℂ] archSmooth ℚ 3) (W : V) (h : tr W.1 ∈ tV V) :
    U' U ⟨tr W.1, h⟩ = S (U W) :=
  U'_e U W

theorem exists_e {V : Submodule ℂ (G3 → ℂ)} (X : tV V) : ∃ W : V, X = e V W :=
  ⟨(e V).symm X, by simp⟩

theorem continuous_lift {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3)
    (hU : IsLiftU V hV U) (W : V) : Continuous (U W : G3 → ℂ) := by
  refine FourierWhittaker.IsUSmooth.continuous (n := 3) (K := ℚ) ⟨(U W).2, ?_, (hU.1 W).1⟩
  obtain ⟨O, hO⟩ := hV.level W.1 W.2
  refine ⟨O, fun g u hu => ?_⟩
  have h := hU.2.1 W (finEmb ℚ 3 u) g
  have e : (⟨fun x => W.1 (x * finEmb ℚ 3 u), hV.stable _ W.2 _⟩ : V) = W :=
    Subtype.ext (funext fun x => hO x u hu)
  rw [e] at h
  exact h.symm

theorem left_ti {φ : G3 → ℂ} (h : IsLeftInvariant φ) : IsLeftInvariant (fun g : G3 => φ (ti g)) := by
  intro γ g
  show φ (ti (dia γ * g)) = φ (ti g)
  rw [ti_mul, GlobalTheory.T.transposeInv_properties.2.1 γ]
  exact h (ti γ) (ti g)

theorem main : ∀ (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU V hV U →
  ∃ (hV' : WhA (tV V)) (U' : tV V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU (tV V) hV' U' ∧
    ∀ W : V, ∃ hW : tr W.1 ∈ tV V, (U' ⟨tr W.1, hW⟩ : G3 → ℂ) = fun g : G3 => (U W : G3 → ℂ) (ti g) := by
  intro V hV U hU
  have hV' := GlobalTheory.T.whittaker_space_transpose_inverse V hV
  refine ⟨hV', LiftTV.U' U, ⟨?_, ?_, ?_⟩, fun W => ⟨tr_mem W, ?_⟩⟩
  · intro X
    obtain ⟨W, rfl⟩ := exists_e X
    obtain ⟨h1, h2, h3, h4⟩ := hU.1 W
    rw [U'_e]
    refine ⟨left_ti h1, GlobalTheory.T.moderateGrowth_comp_transposeInv _ h2, GlobalTheory.T.cuspidal_comp_transposeInv _ h1 h3, ?_⟩
    funext g
    have := GlobalTheory.T.whittaker_comp_transposeInv _ h1 (continuous_lift hV U hU W) g
    rw [h4] at this
    exact this
  · intro X h g
    obtain ⟨W, rfl⟩ := exists_e X
    have hW' : (fun x => W.1 (x * ti h)) ∈ V := hV.stable _ W.2 _
    have hfun : (fun x => (e V W).1 (x * h)) = tr (fun x => W.1 (x * ti h)) :=
      funext fun x => GlobalTheory.T.whittaker_transform_properties.2.1 W.1 h x
    have hel : (⟨fun x => (e V W).1 (x * h), hV'.stable _ (e V W).2 h⟩ : tV V)
        = e V ⟨fun x => W.1 (x * ti h), hW'⟩ := Subtype.ext hfun
    rw [hel, U'_e, U'_e, S_apply, S_apply, hU.2.1 W (ti h) (ti g), ti_mul]
  · intro X i j
    obtain ⟨W, rfl⟩ := exists_e X
    have hWa : IsArchSmooth W.1 := hV.arch W.1 W.2
    have hc := GlobalTheory.T.archSmooth_comp_transposeInv W.1 hWa (w3 * ti (dia dl3))
    have hl : ((EA j i ⟨W.1, hWa⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ V := hV.lie _ W.2 j i
    set W2 : V := ⟨_, hl⟩ with hW2
    have hel : (⟨_, hV'.lie _ (e V W).2 i j⟩ : tV V) = e V (-W2) := by
      apply Subtype.ext
      have a1 : (⟨(e V W).1, hV'.arch _ (e V W).2⟩ : archSmooth ℚ 3) = ⟨_, hc⟩ :=
        Subtype.ext (tr_eq W.1)
      simp only [a1]
      rw [GlobalTheory.T.lie_action_comp_transposeInv ⟨W.1, hWa⟩ _ i j hc]
      funext g
      show _ = tr (-W2.1) g
      rw [GlobalTheory.T.whittaker_transform_properties.1]
      rfl
    rw [hel, U'_e, U'_e, map_neg]
    have h3 : U W2 = EA j i (U W) := hU.2.2 W j i
    rw [h3]
    apply Subtype.ext
    have hb := GlobalTheory.T.archSmooth_comp_transposeInv (U W) (U W).2 1
    have b1 : S (U W) = ⟨fun g : G3 => (U W : G3 → ℂ) (1 * ti g), hb⟩ :=
      Subtype.ext (funext fun g => by simp [S_apply])
    rw [b1, GlobalTheory.T.lie_action_comp_transposeInv (U W) 1 i j]
    funext g
    simp [S_apply]
  · have := U'_tr U W (tr_mem W)
    rw [this]
    rfl

end GlobalTheory.CompanionTheory.UnfoldingAlt.LiftTV
end
end
