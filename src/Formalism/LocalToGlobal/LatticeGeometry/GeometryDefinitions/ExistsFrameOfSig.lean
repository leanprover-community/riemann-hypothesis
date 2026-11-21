import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

section
noncomputable section

open Module Matrix

namespace Formalism.L2.Geo.Def.G1

section Frame

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]

theorem dual_frame (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    ∃ (n : ℕ) (g w : Fin n → V), (∀ i, g i ∈ L) ∧ (∀ i, w i ∈ Formalism.HermitianLatticesTheory.dual h L) ∧
      ∀ z : V, z = ∑ i, h (w i) z • g i := by
  classical
  have hsp : Submodule.span K (L : Set V) = ⊤ := hL.span_eq_top

  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  haveI : Fintype s := (LinearIndependent.setFinite hli).fintype
  let b : Module.Basis s K V := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  have hbL : ∀ j, b j ∈ L := fun j => by
    rw [show b j = (j : V) from Module.Basis.mk_apply hli _ j]; exact hsL j.2
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbs' : ∀ j k, h (bs j) (b k) = if k = j then 1 else 0 := fun j k => by
    rw [← hs.eq (b k) (bs j), hbs k j]; split_ifs <;> simp
  have hcoord : ∀ z : V, z = ∑ j, h (bs j) z • b j := by
    have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ j, (h (bs j)).smulRight (b j) := by
      apply b.ext; intro k
      simp [LinearMap.smulRight_apply, hbs']
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin

  haveI : Module.Finite R L := Module.Finite.iff_fg.2 hL.fg
  haveI : Module.Flat R L := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : algebraMap R K (a : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have h1 : algebraMap R K (a : R) • (x : V) = 0 := by
      rw [algebraMap_smul]
      have := congrArg Subtype.val hax
      simpa [Submonoid.smul_def] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left ha0)
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let g : Fin n → V := fun i => (π (fun j => if i = j then 1 else 0) : V)
  let fi : Fin n → L →ₗ[R] R := fun i => (LinearMap.proj i).comp sec
  have hzL : ∀ z : L, (z : V) = ∑ i, fi i z • g i := by
    intro z
    have h1 : π (sec z) = z := LinearMap.congr_fun hsec z
    calc (z : V) = ((π (sec z) : L) : V) := by rw [h1]
      _ = _ := by rw [LinearMap.pi_apply_eq_sum_univ π (sec z)]; simp [fi, g]

  let w : Fin n → V := fun i => ∑ j, star (algebraMap R K (fi i ⟨b j, hbL j⟩)) • bs j
  have hw_b : ∀ i k, h (w i) (b k) = algebraMap R K (fi i ⟨b k, hbL k⟩) := by
    intro i k
    simp only [w, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbs',
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [starRingEnd_apply, star_star]
  have hw_L : ∀ i (z : L), h (w i) z = algebraMap R K (fi i z) := by
    intro i z
    obtain ⟨d, hd⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ (fun j => h (bs j) (z : V))
    choose a ha using fun j => hd j (Finset.mem_univ j)
    have hdzV : (d : R) • (z : V) = ∑ j, a j • b j := by
      conv_lhs => rw [hcoord (z : V)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_assoc, ← ha j, algebraMap_smul]
    have hdz : (d : R) • z = ∑ j, a j • (⟨b j, hbL j⟩ : L) := Subtype.ext (by simp [hdzV])
    have hd0 : algebraMap R K (d : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have L1 : algebraMap R K d * h (w i) z =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, algebraMap_smul, hdzV, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← algebraMap_smul K (a j) (b j), LinearMap.map_smul, hw_b, smul_eq_mul]
    have L2 : algebraMap R K d * algebraMap R K (fi i z) =
        ∑ j, algebraMap R K (a j) * algebraMap R K (fi i ⟨b j, hbL j⟩) := by
      rw [← map_mul, ← smul_eq_mul, ← LinearMap.map_smul, hdz, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, map_mul]
    exact mul_left_cancel₀ hd0 (L1.trans L2.symm)
  refine ⟨n, g, w, fun i => (π _).2, ?_, ?_⟩
  · intro i
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    intro y hy
    rw [Submodule.mem_one, ← hs.eq (w i) y, hw_L i ⟨y, hy⟩]
    obtain ⟨r, hr⟩ := hstar (fi i ⟨y, hy⟩)
    exact ⟨r, by rw [hr]; rfl⟩
  · have hlin : (LinearMap.id : V →ₗ[K] V) = ∑ i, (h (w i)).smulRight (g i) := by
      apply LinearMap.ext_on hsp
      intro z hz
      simp only [LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
      calc z = ∑ i, fi i ⟨z, hz⟩ • g i := hzL ⟨z, hz⟩
        _ = ∑ i, h (w i) z • g i := Finset.sum_congr rfl fun i _ => by
          rw [show h (w i) z = h (w i) ((⟨z, hz⟩ : L) : V) from rfl, hw_L i ⟨z, hz⟩,
            algebraMap_smul]
    intro z
    simpa using congrArg (fun F : V →ₗ[K] V => F z) hlin

end Frame

section Coord

variable {K : Type} [Field K] [StarRing K]

theorem hform_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = Formalism.UG.hform (starRingEnd K) H x y := by
  simp [Formalism.DivisionValues.hform, Formalism.UG.hform, Matrix.toLinearMapₛₗ₂'_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def IsFrame {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K) : Prop :=
  ∀ a b, ∑ i, g i a * ∑ c, star (w i c) * H c b = if a = b then 1 else 0


theorem IsFrame.map {n k : ℕ} {H : Matrix (Fin n) (Fin n) K} {g w : Fin k → Fin n → K} (hf : IsFrame H g w)
    {A : Type} [CommRing A] (φ : K →+* A) (σ : A →+* A) (hσ : ∀ x, σ (φ x) = φ (star x)) (z : Fin n → A) :
    z = ∑ i, Formalism.UG.hform σ (H.map φ) (fun c => φ (w i c)) z • (fun a => φ (g i a)) := by
  funext a
  have e1 : ∀ d, φ (∑ i, g i a * ∑ c, star (w i c) * H c d) = if a = d then 1 else 0 := fun d => by
    rw [hf a d]; split_ifs <;> simp
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.hform, Matrix.map_apply, hσ]
  calc z a = ∑ d, z d * (if a = d then 1 else 0) := by simp
    _ = ∑ d, z d * φ (∑ i, g i a * ∑ c, star (w i c) * H c d) := by simp only [e1]
    _ = _ := by
      simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Coord

end Formalism.L2.Geo.Def.G1
end
end

section
noncomputable section

open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.G1

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem star_int (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (star (algebraMap (𝓞 E) E r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem mem_one_iff (e : E) : e ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ e := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨e, h⟩, rfl⟩



end Glob

end Formalism.L2.Geo.Def.G1
end
end

section
noncomputable section

open Module Matrix NumberField Formalism.BasicNotions Formalism.HN

namespace Formalism.L2.Geo.Def.G1

section Line

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

section Single

variable {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

omit [IsTotallyComplex K] [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem majAt_self (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (e : V) :
    (Formalism.HermitianLatticesTheory.majAt b X v e e).re = Formalism.HermitianLatticesTheory.normAt b X v e ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring


end Single

theorem lcv_eq_mu {n : ℕ} (hn : 0 < n) (Y : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hY : ∀ v, IsUnit (Y v).det)
    (T : Submodule (𝓞 K) (Fin n → K)) (hfg : T.FG) (hrk : rkK T = n) :
    Formalism.DivisionValues.lcv Y T = -(n : ℝ) * muDef (Pi.basisFun K (Fin n)) Y T := by
  have hsp : Submodule.span K (T : Set (Fin n → K)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have : finrank K (Submodule.span K (T : Set (Fin n → K))) = n := hrk
    rw [this]; simp
  let B : HLat K := { V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := Y, L := T }
  have hB : B.Good := ⟨hY, hfg, hsp⟩
  have hBr : B.rank = n := hrk
  have h := bridge_hn_mu_holds K B hB (by rw [hBr]; exact hn)
  rw [hBr] at h
  have h1 : B.mu = muDef (Pi.basisFun K (Fin n)) Y T := rfl
  have h2 : B.lcv = Formalism.DivisionValues.lcv Y T := rfl
  rw [← h1, ← h2, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Line

end Formalism.L2.Geo.Def.G1
end
end

section
noncomputable section

open Module Matrix NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.HN
open scoped TensorProduct

namespace Formalism.L2.Geo.Def.G1

section Frames

theorem exists_frame_of_sig {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℕ)
    (h : HasSignature M p 0) : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ := (P : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ) with hA
  have hJ : Jpq p 0 = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  have hcT : cT (starRingEnd ℂ) A = A.conjTranspose := by
    ext i j; simp [cT, Matrix.conjTranspose_apply]
  rw [hJ, hcT] at hP
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hM' : M.reindex e e = (A⁻¹).conjTranspose * A⁻¹ := by
    have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdetA
    calc M.reindex e e = (A * A⁻¹).conjTranspose * M.reindex e e * (A * A⁻¹) := by
          rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (A⁻¹).conjTranspose * (A.conjTranspose * M.reindex e e * A) * A⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (A⁻¹).conjTranspose * A⁻¹ := by rw [hP, Matrix.mul_one]
  refine ⟨A.submatrix e e, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]; exact hdetA
  · rw [Matrix.inv_submatrix_equiv, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← hM']
    ext i j
    simp

theorem frameOf_spec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M) :
    IsUnit (frameOf M).det ∧ ((frameOf M)⁻¹).conjTranspose * (frameOf M)⁻¹ = M := by
  rw [frameOf, dif_pos h]
  exact h.choose_spec

end Frames

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open Formalism.L2.Herm

theorem crdLat_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) : crd S x ∈ crdLat S L ↔ x ∈ L := by
  simp only [crdLat, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [(crd S).injective hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem crdLat_lattice (S : HSpace E) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice E (crdLat S L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have hset : (crdLat S L : Set (Fin S.rank → E)) =
      (crd S : S.V →ₗ[E] (Fin S.rank → E)) '' (L : Set S.V) := by
    ext u; simp [crdLat]
  rw [hset, Submodule.span_image, hL.span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (crd S).surjective

end Space

section Twist

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Twist

end Formalism.L2.Geo.Def.G1
end
end
