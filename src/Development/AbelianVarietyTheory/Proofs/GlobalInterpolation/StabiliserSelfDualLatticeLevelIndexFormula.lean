import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualStabiliserIndex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexConjLevelVL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MyTiedNotMeasTupleTied
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

theorem isSelfDualLat_iff {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]
    (σ : E →+* E) (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) :
    SelfDualStabiliserIndex.IsSelfDualLat σ J N ↔ SelfDualLatticeIndex.IsSelfDualLat σ J N :=
  and_congr_right fun _ => and_congr_right fun _ => eq_comm

theorem self_dual_lattice_iff_x0 (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    (letI := D.host.cmStar
     SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N) ↔
      SelfDualLatticeIndex.IsSelfDualDefiniteLattice D N :=
  isSelfDualLat_iff _ _ _

theorem indexAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    SelfDualStabiliserIndex.IndexAt D Lv u ↔ SelfDualLatticeIndex.IndexAt D Lv u :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun N =>
    imp_congr (self_dual_lattice_iff_x0 D N) Iff.rfl

theorem indexKU_iff : SelfDualStabiliserIndex.IndexKU ↔ SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => indexAt_iff D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel
end
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelfDualFrame

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

def sw (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) ≃+* LocAlg v :=
  (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem mem_intV_iff (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    z ∈ intV E v ↔ sw v z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le
      (t := (locOrder v).toSubring.comap (sw v).toRingHom)).2 ?_ hz
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact locEmb_mem_locOrder v x
    · exact (locOrder v).algebraMap_mem ⟨a.1, a.2⟩
  · intro hz
    have key : ∀ y ∈ locOrder v, (sw v).symm y ∈ intV E v := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact Subring.subset_closure (Or.inl ⟨⟨a, a, rfl⟩, rfl⟩)
      | algebraMap r => exact Subring.subset_closure (Or.inr ⟨⟨r.1, r.2⟩, rfl⟩)
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    simpa using key _ hz

theorem mem_latS_iff {r : ℕ} (N : Submodule (𝓞 E) (Fin r → E))
    (x : Fin r → E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (intV E v) N ↔
      (fun i => sw v (x i)) ∈ locLattice v N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact (locLattice v N).zero_mem
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext i
      simp
    | smul c x _ hx =>
      have := smul_mem_locLattice v ((mem_intV_iff v _).1 c.2) hx
      convert this using 1
      funext i
      exact map_mul (sw v) _ _
  · intro hx
    have key : ∀ y ∈ locLattice v N, (fun i => (sw v).symm (y i)) ∈
        latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
          (intV E v) N := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have := add_mem hx hy
        convert this using 1
        funext i
        simp
      | smul c x _ hx =>
        have hc : (sw v).symm (algebraMap _ (LocAlg v) c) ∈ intV E v :=
          (mem_intV_iff v _).2 (by simpa using (locOrder v).algebraMap_mem c)
        have := Submodule.smul_mem _ (⟨_, hc⟩ : intV E v) hx
        convert this using 1
        funext i
        rw [Pi.smul_apply, Algebra.smul_def]
        exact map_mul (sw v).symm _ _
    simpa using key _ hx

theorem sw_sigR (hc : CMData (maximalRealSubfield E) E)
    (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    sw v (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E)) z) = locConj v (sw v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_frame_cm (hc : CMData (maximalRealSubfield E) E) {r : ℕ}
    (J : Matrix (Fin r) (Fin r) E) (hJ : IsHerm (hc.sig : E →+* E) J) (hd : IsUnit J.det)
    (N : Submodule (𝓞 E) (Fin r → E))
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (hc.sig : E →+* E) J N) :
    ∃ b : GL (Fin r) (E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)),
      cT (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E))) b.1 *
        J.map (inclE (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))) *
          b.1 = 1 ∧
      ∀ x, x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
        (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v := by
  have := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (Jᵀ a b) = Jᵀ b a :=
    fun a b => congrFun (congrFun hJ a) b
  have hd' : Jᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hd.ne_zero
  have hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = hform (hc.sig : E →+* E) J y x := by
    intro x y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm hform
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change x j * J i j * ReciprocityTheory.ChartRestriction.G.FD.cc (y i) = ReciprocityTheory.ChartRestriction.G.FD.cc (y i) * J i j * x j
    ring
  have hint : ∀ a : E, a ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ a := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩; exact b.isIntegral_coe
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
  have hsd : ∀ x, x ∈ N ↔ ∀ y ∈ N, IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y) := by
    intro x
    have : x ∈ dualSet (hc.sig : E →+* E) J N ↔ x ∈ N := by rw [hN.2.2]; rfl
    rw [← this]
    simp only [hh, ← hint]
    rfl
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd'
    ⟨Module.Finite.iff_fg.1 hN.1, hN.2.1⟩ hsd v
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  have hb : ∀ g : GL (Fin r) (LocAlg v), (bc (sw v).symm.toRingHom g).1.map (sw v) = g.1 := by
    intro g
    ext i j
    exact (sw v).apply_symm_apply _
  refine ⟨bc (sw v).symm.toRingHom h, ?_, fun x => ?_⟩
  · apply Matrix.map_injective (f := (sw v).toRingHom) (sw v).injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h3]
    congr 1
    · congr 1
      ext i j
      exact (sw_sigR v hc _).trans (congrArg (locConj v) ((sw v).apply_symm_apply _))
    · exact hb h
  · rw [mem_latS_iff, h2, ← map_inv]
    refine forall_congr' fun i => ?_
    rw [mem_intV_iff, ← hb h⁻¹]
    have := RingHom.map_mulVec (sw v).toRingHom (bc (sw v).symm.toRingHom h⁻¹).1 x i
    exact Iff.of_eq (congrArg (· ∈ locOrder v) this.symm)

end CM

theorem exists_frame : ∀ (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)), letI := D.host.cmStar; GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N → ∃ b : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F), cT (Formalism.UG.sigR D.sp.cm.sig (v.adicCompletion D.host.F)) b.1 * D.sp.gram0.map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * b.1 = 1 ∧ ∀ x, x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV D.host.E v := by
  intro D N v hN
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  exact exists_frame_cm v D.sp.cm D.sp.gram0 D.sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit D.sp) N hN

end GlobalTheory.SelfDualFrame
end
end

section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

namespace GlobalTheory.CompletionAut

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem exists_natCast_valued_lt_one :
    ∃ p : ℕ, (p : v.adicCompletion F) ≠ 0 ∧ Valued.v (p : v.adicCompletion F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
    exact Nat.cast_ne_zero.2 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · have h := Ideal.absNorm_mem v.asIdeal
    have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F)
          (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) := by simp
    rw [h2]
    erw [valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem v _).2 h

theorem exists_pow_eq_of_mem {p : ℕ} (hp : Valued.v (p : v.adicCompletion F) < 1) (e : ℕ)
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ y : v.adicCompletion F, y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1) := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set R := v.adicCompletionIntegers F
  have hpm : (p : R) ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (p : v.adicCompletion F) = 1 := by simpa using h
    exact hp.ne h'
  let c : R := 1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ (p * e + 1) - C c) (monic_X_pow_sub_C c (Nat.succ_ne_zero _)) 1
    (by
      simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow, c]
      have : (1 : R) - (1 + p * (⟨x, hx⟩ : R) ^ (p * e + 1)) =
          p * (-(⟨x, hx⟩ : R) ^ (p * e + 1)) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hpm)
    (by
      have h0 : Ideal.Quotient.mk (maximalIdeal R) (p : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hpm
      rw [map_natCast] at h0
      simp [derivative_X_pow, h0])
  refine ⟨a, ?_⟩
  have h1 : a ^ (p * e + 1) = c := by
    simpa [IsRoot, sub_eq_zero] using ha
  have := congrArg (fun z : R => (z : v.adicCompletion F)) h1
  simpa [c] using this

theorem mem_of_pow_eq {p e : ℕ} (he : 0 < e)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-(e : ℤ))) (hp0 : p ≠ 0)
    {x y : v.adicCompletion F} (h : y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1)) :
    x ∈ v.adicCompletionIntegers F := by
  rw [mem_adicCompletionIntegers]
  by_contra hx
  push Not at hx
  have hx0 : Valued.v x ≠ 0 := (zero_lt_one.trans hx).ne'
  set l := p * e + 1 with hl
  have hle : e < l := by
    have : e ≤ p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero hp0)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hm0 : 0 < m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; exact hx
  have h1 : Valued.v ((p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [map_mul, map_pow, hp, hm, ← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]
  have hpos : 0 < -(e : ℤ) + l * m := by
    have : (e : ℤ) < l := by exact_mod_cast hle
    nlinarith
  have h2 : Valued.v (1 + (p : v.adicCompletion F) * x ^ l) = WithZero.exp (-(e : ℤ) + l * m) := by
    rw [← h1]
    apply Valuation.map_add_eq_of_lt_right
    rw [h1, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact hpos
  rw [← h, map_pow] at h2
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2
    exact WithZero.exp_ne_zero h2.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v y = WithZero.exp k := ⟨_, (WithZero.exp_log hy0).symm⟩
  rw [hk, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  have hd : (l : ℤ) ∣ (e : ℤ) := ⟨m - k, by linear_combination h2⟩
  have := Nat.le_of_dvd he (Int.natCast_dvd_natCast.1 hd)
  omega

theorem map_mem (θ : v.adicCompletion F →+* v.adicCompletion F) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : θ x ∈ v.adicCompletionIntegers F := by
  obtain ⟨p, hp0, hp⟩ := exists_natCast_valued_lt_one v
  have hv0 : Valued.v (p : v.adicCompletion F) ≠ 0 := by simpa using hp0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (p : v.adicCompletion F) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  have hm0 : m < 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hp; exact hp
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m by omega)
  obtain ⟨y, hy⟩ := exists_pow_eq_of_mem v hp e hx
  refine mem_of_pow_eq v (p := p) (e := e) (y := θ y) (by omega) (by rw [hm, ← he, neg_neg])
    (by rintro rfl; simp at hp0) ?_
  simpa using congrArg θ hy

end GlobalTheory.CompletionAut

namespace GlobalTheory

theorem ringEquiv_adicCompletion_mem_integers_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (θ : v.adicCompletion F ≃+* v.adicCompletion F)
    (x : v.adicCompletion F) :
    θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F :=
  ⟨fun h => by simpa using CompletionAut.map_mem v θ.symm.toRingHom h,
    fun h => CompletionAut.map_mem v θ.toRingHom h⟩

end GlobalTheory
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.SplitIntegers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem conj_tmul (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    Formalism.UG.sigR hc.sig R (a ⊗ₜ[F] y) = star a ⊗ₜ[F] y := rfl

omit [NumberField F] [NumberField E] [StarRing E] in
theorem algebraMap_tmul {R : Type} [CommRing R] [Algebra F R] (c : F) (y : R) :
    (algebraMap F E c) ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (algebraMap F R c * y) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

theorem exists_add_conj (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    ∃ p : R, z + Formalism.UG.sigR hc.sig R z = (1 : E) ⊗ₜ[F] p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, h⟩ := (hc.fixed (a + star a)).1 (by simp [add_comm])
    exact ⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add, TensorProduct.tmul_add, ← hp, ← hq]; ring

theorem exists_of_conj_eq (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] {z : E ⊗[F] R}
    (hz : Formalism.UG.sigR hc.sig R z = z) : ∃ p : R, (1 : E) ⊗ₜ[F] p = z := by
  obtain ⟨p, hp⟩ := exists_add_conj hc z
  rw [hz, ← two_smul F z] at hp
  refine ⟨(2⁻¹ : F) • p, ?_⟩
  rw [TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_diag (hc : CMData F E) {K : Type} [Field K] [Algebra F K]
    (φ : E ⊗[F] K ≃+* K × K) (hφ : ∀ x, φ (Formalism.UG.sigR hc.sig K x) = swapR _ (φ x)) :
    ∃ θ : K ≃+* K, ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (θ y, θ y) := by
  let f : K →+* K := ((RingHom.fst K K).comp φ.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom
  have hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y) := fun y => by
    have h := hφ ((1 : E) ⊗ₜ[F] y)
    rw [conj_tmul, star_one] at h
    have h2 := congrArg Prod.snd h
    exact Prod.ext rfl h2
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩
  obtain ⟨p, hp⟩ := exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by
    rw [hφ, φ.apply_symm_apply]; rfl))
  refine ⟨p, ?_⟩
  have := hf p
  rw [hp, φ.apply_symm_apply] at this
  exact (congrArg Prod.fst this).symm

theorem mem_of_isIntegral (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : IsIntegral ℤ x) : x ∈ v.adicCompletionIntegers F := by
  have hi : IsIntegral (v.adicCompletionIntegers F) x := hx.tower_top
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

omit [NumberField E] [StarRing E] [Algebra F E] in
theorem map_mem {S : Type} (v : HeightOneSpectrum (𝓞 F)) [FunLike S E (v.adicCompletion F)]
    [RingHomClass S E (v.adicCompletion F)] (g : S) (a : 𝓞 E) :
    g (algebraMap (𝓞 E) E a) ∈ v.adicCompletionIntegers F :=
  mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ)
    (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))

end GlobalTheory.SplitIntegers

namespace GlobalTheory

open SplitIntegers

theorem mem_intV_iff_of_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)), (∀ (θ : v.adicCompletion F ≃+* v.adicCompletion F) (x : v.adicCompletion F), θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F) → ∀ (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, φ (Formalism.UG.sigR hc.sig (v.adicCompletion F) x) = swapR _ (φ x)) → ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ hc v hθ φ hφ
  obtain ⟨θ, hd⟩ := exists_diag hc φ hφ
  have hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F :=
    fun y hy => (hθ θ.symm y).2 hy
  let ι : E →+* v.adicCompletion F × v.adicCompletion F := φ.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
  have hι : ∀ a : 𝓞 E,
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F := fun a =>
    ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩
  intro x
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · exact hι a
      · beta_reduce
        rw [hd]
        exact ⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | one => rw [map_one]; exact ⟨one_mem _, one_mem _⟩
    | add x y _ _ hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.Mass.Genus.exists_over (E := E) v
    obtain ⟨w, t, ht, hwt⟩ := hc.cmUnram.2.2 P hP
    obtain ⟨s, hs⟩ := (hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by
      rw [map_mul, map_sub, ht, star_mul, star_sub, star_star]; ring)
    have hsi : IsIntegral ℤ s := by
      have := ((w - t) * (w - t)).isIntegral_coe
      rw [← hs] at this
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this
    let s' : 𝓞 F := ⟨s, hsi⟩
    have hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t) := RingOfIntegers.ext hs
    have hsv : s' ∉ v.asIdeal := fun h => by
      rw [← hPv, Ideal.mem_comap, hs'] at h
      exact hwt ((hP.isPrime.mem_or_mem h).elim id id)
    obtain ⟨u, hu⟩ := ((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv
    have hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1 :=
      congrArg Subtype.val hu
    obtain ⟨hα, hβ⟩ := hι w
    have e1 := hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)
    rw [conj_tmul, ← ht] at e1
    have e2 := hd (algebraMap F (v.adicCompletion F) s * 1)
    rw [← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub,
      e1] at e2
    generalize hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2
    obtain ⟨α, β⟩ := W
    have e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s) := congrArg Prod.fst e2
    have e4 : θ u * ((α - β) * (α - β)) = 1 := by rw [e3, ← map_mul, hu', map_one]
    have hθu : θ u ∈ v.adicCompletionIntegers F := (hθ θ u).2 u.2
    set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef
    have hcm : c ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))
    have hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) +
        ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) := by
      apply φ.injective
      rw [map_add, map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · change (φ x).1 = (φ x).1 - c * α + c * α
        ring
      · change (φ x).2 = (φ x).1 - c * α + c * β
        rw [hcdef]
        linear_combination ((φ x).1 - (φ x).2) * e4
    rw [hx]
    refine add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩))
      (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩))
        (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))

end GlobalTheory
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem stabGL_iff_conj_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n]
    [DecidableEq n] (b : GL n A) (Λ : Submodule S (n → A))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) (g : GL n A) :
    g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ stabGL (stdLat (n := n) (A := A) S) := by
  have key : ∀ x : n → A, x ∈ Λ ↔ (b⁻¹).1 *ᵥ x ∈ stdLat (n := n) (A := A) S := fun x => by
    rw [hΛ, Formalism.UG.P.afsplit_mem_stdLat]
  constructor
  · intro hg y
    have h := hg (b.1 *ᵥ y)
    rw [key, key] at h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.val_mul,
      Matrix.mul_assoc] using h
  · intro hg x
    have h := hg ((b⁻¹).1 *ᵥ x)
    rw [key, key]
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.mul_one, Units.val_mul,
      Matrix.mul_assoc] using h

theorem conj_mem_UJ_one {A : Type} [CommRing A] (τ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n A) (b : GL n A) (hb : cT τ b.1 * J * b.1 = 1)
    (g : GL n A) (hg : g ∈ UJ τ J) : b⁻¹ * g * b ∈ UJ τ (1 : Matrix n n A) := by
  have hg' : cT τ g.1 * J * g.1 = J := hg
  have cm : ∀ M N : Matrix n n A, cT τ (M * N) = cT τ N * cT τ M := fun M N => by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have c1 : cT τ (1 : Matrix n n A) = 1 := by
    simp only [cT, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have hJ : cT τ (b⁻¹).1 * (b⁻¹).1 = J := by
    calc cT τ (b⁻¹).1 * (b⁻¹).1 = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by
          rw [hb, Matrix.mul_one]
      _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
          rw [cm]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, c1, Matrix.one_mul, Matrix.mul_one]
  change cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1 = 1
  calc cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1
      = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
        simp only [Units.val_mul, cm, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hg', hb]

theorem split_stabGL_iff_mem_range :
    ∀ (A K : Type) [CommRing A] [Field K] (O : ValuationSubring K) (S : Subring A) (τ : A →+* A) (φ : A ≃+* K × K), (∀ x, φ (τ x) = swapR K (φ x)) → (∀ x, x ∈ S ↔ (φ x).1 ∈ O ∧ (φ x).2 ∈ O) → ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A) (b : GL n A) (Λ : Submodule S (n → A)), cT τ b.1 * J * b.1 = 1 → (∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) → ∀ g ∈ UJ τ J, g ∈ stabGL Λ ↔ (bc ((RingHom.fst K K).comp φ.toRingHom) b)⁻¹ * bc ((RingHom.fst K K).comp φ.toRingHom) g * bc ((RingHom.fst K K).comp φ.toRingHom) b ∈ (bc (n := n) (algebraMap O K)).range := by
  intro A K _ _ O S τ φ hτ hS n _ _ J b Λ hb hΛ g hg
  have hU := conj_mem_UJ_one τ J b hb g hg
  rw [stabGL_iff_conj_stdLat S b Λ hΛ g, ← map_inv, ← map_mul, ← map_mul]
  generalize b⁻¹ * g * b = h at hU
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hOr : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [Formalism.UG.P.afsplit_stab_iff, Formalism.UG.P.levelvsplit_mem_range_iff _ hinj, ← map_inv,
    Formalism.UG.P.levelvsplit_coe_bc, Formalism.UG.P.levelvsplit_coe_bc]
  simp only [hOr, hS]
  have main : ∀ k : GL n A, k ∈ UJ τ (1 : Matrix n n A) → ∀ i j,
      (φ (k.1 i j)).2 = (φ ((k⁻¹).1 j i)).1 := by
    intro k hk i j
    have rel := Formalism.UG.P.levelvsplit_unitary τ φ hτ _ k hk
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at rel
    have hk1 : k.1.map ((RingHom.fst K K).comp φ.toRingHom) *
        (k⁻¹).1.map ((RingHom.fst K K).comp φ.toRingHom) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have s := Formalism.UG.P.levelvsplit_solve 1 1 _ _ _ (Matrix.mul_one _) hk1 rel
    rw [Matrix.one_mul, Matrix.mul_one] at s
    exact congrFun (congrFun s i) j
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · rw [main h hU]; exact h2 j i
    · rw [main h⁻¹ (inv_mem hU), inv_inv]; exact h1 j i

end GlobalTheory
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.CongIndex

theorem relIndex_congPre (O K : Type) [CommRing O] [IsLocalRing O] [CommRing K] (ι : O →+* K)
    (hι : Function.Injective ι) (n : ℕ) (H : Subgroup (GL (Fin n) (O ⧸ IsLocalRing.maximalIdeal O))) :
    (congPre ι (IsLocalRing.maximalIdeal O) H).relIndex (bc (n := Fin n) ι).range = H.index := by
  have hinj : Function.Injective (bc (n := Fin n) ι) := by
    intro g h e
    apply Units.ext
    ext a b
    apply hι
    exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) e
  have hs : Function.Surjective (redGL (n := Fin n) (IsLocalRing.maximalIdeal O)) :=
    GlobalTheory.MeasTupleEq.map_residue_surjective O n
  unfold congPre
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ hs]

end GlobalTheory.CongIndex
end

section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Proof.StabilizerIndex

lemma index_field (F : Type) [Field F] [Finite F] (k : ℕ) (φ : Fin k → F) (hφ : φ ≠ 0) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = Nat.card F ^ k - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h := Formalism.LogVandermondeBounds.StandardLattice.cardStabilizerVector F k φ hφ
  have hcm := (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).card_mul_index
  have hc : Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ) =
      Nat.card {A : GL (Fin k) F // Matrix.vecMul φ (A : Matrix (Fin k) (Fin k) F) = φ} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun A => Iff.rfl))
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← hc, ← hcm] at h
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm

theorem index_stabRow : ∀ (κ : Type) [CommRing κ] (T k : ℕ), T.Prime → Nat.card κ = T →
    ∀ φ : Fin k → κ, φ ≠ 0 →
      (((GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index : ℕ) : ℝ) = (T : ℝ) ^ k - 1 := by
  intro κ _ T k hT hcard φ hφ
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hcard ▸ hT.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod T ≃+* κ := ZMod.ringEquivOfPrime κ hT (by rw [← Nat.card_eq_fintype_card, hcard])
  have hF : IsField κ := MulEquiv.isField (Field.toIsField (ZMod T)) e.symm.toMulEquiv
  have h := @index_field κ hF.toField _ k φ hφ
  have h' : (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow φ).index = T ^ k - 1 := by
    rw [← hcard]; exact h
  rw [h', Nat.cast_sub (Nat.one_le_pow _ _ hT.pos)]
  push_cast
  rfl

end GlobalTheory.Proof.StabilizerIndex
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.LevelIndex

section Group

variable {G G' : Type} [Group G] [Group G']

theorem relIndex_eq_of_symm {U K K' : Subgroup G} (h : K'.relIndex K = K.relIndex K') (h1 : U ≤ K)
    (h2 : U ≤ K') : U.relIndex K = U.relIndex K' := by
  rw [← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K (le_inf h1 h2) inf_le_left,
    ← Subgroup.relIndex_mul_relIndex U (K ⊓ K') K' (le_inf h1 h2) inf_le_right,
    Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, h]

theorem mem_map_conj {K : Subgroup G} {γ g : G} :
    g ∈ K.map (MulAut.conj γ).toMonoidHom ↔ γ⁻¹ * g * γ ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

def pull (H : Subgroup G) (p : G →* G') (b : G') (X : Subgroup G') : Subgroup G :=
  H ⊓ X.comap ((MulAut.conj b⁻¹).toMonoidHom.comp p)

theorem mem_pull {H : Subgroup G} {p : G →* G'} {b : G'} {X : Subgroup G'} {g : G} :
    g ∈ pull H p b X ↔ g ∈ H ∧ b⁻¹ * p g * b ∈ X := by
  simp [pull]

theorem pull_mono (H : Subgroup G) (p : G →* G') (b : G') {X Y : Subgroup G'} (h : X ≤ Y) :
    pull H p b X ≤ pull H p b Y := fun _ hg => mem_pull.2 ⟨(mem_pull.1 hg).1, h (mem_pull.1 hg).2⟩

theorem relIndex_pull {H : Subgroup G} {p : G →* G'} (hs : ∀ y, ∃ g ∈ H, p g = y) (b : G')
    (X Y : Subgroup G') : (pull H p b X).relIndex (pull H p b Y) = X.relIndex Y := by
  have h1 : (pull H p b X).relIndex (pull H p b Y) =
      (X.comap ((MulAut.conj b⁻¹).toMonoidHom.comp p)).relIndex (pull H p b Y) := by
    unfold Subgroup.relIndex
    congr 1
    ext g
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  rw [h1, Subgroup.relIndex_comap]
  congr 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.2
  · intro hy
    obtain ⟨g, hg, e⟩ := hs (b * y * b⁻¹)
    refine ⟨g, mem_pull.2 ⟨hg, ?_⟩, ?_⟩
    · simpa [e, mul_assoc] using hy
    · simp [e, mul_assoc]

theorem map_conj_pull {H : Subgroup G} (p : G →* G') (b : G') (X : Subgroup G') {γ : G} (hγ : γ ∈ H) :
    (pull H p b X).map (MulAut.conj γ).toMonoidHom = pull H p (p γ * b) X := by
  ext g
  rw [mem_map_conj, mem_pull, mem_pull]
  refine and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ?_
  · have := mul_mem (mul_mem hγ h) (inv_mem hγ)
    simpa [mul_assoc] using this
  · simp [mul_assoc]

end Group

section Frames

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_inv_mem_UJ {τ : A →+* A} {J : Matrix n n A} {b b' : GL n A} (hb : cT τ b.1 * J * b.1 = 1)
    (hb' : cT τ b'.1 * J * b'.1 = 1) : b' * b⁻¹ ∈ UJ τ J := by
  change cT τ (b' * b⁻¹).1 * J * (b' * b⁻¹).1 = J
  calc cT τ (b' * b⁻¹).1 * J * (b' * b⁻¹).1
      = cT τ (b⁻¹).1 * (cT τ b'.1 * J * b'.1) * (b⁻¹).1 := by
        rw [Units.val_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by rw [hb, hb']
    _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

theorem map_conj_level {S : Subring A} {τ : A →+* A} {J : Matrix n n A} {Λ Λ' : Submodule S (n → A)}
    {γ : GL n A} (hγ : γ ∈ UJ τ J) (h : ∀ x, x ∈ Λ ↔ γ.1 *ᵥ x ∈ Λ') :
    (level τ J Λ).map (MulAut.conj γ).toMonoidHom = level τ J Λ' := by
  ext g
  rw [mem_map_conj]
  have e : ∀ x, γ.1 *ᵥ ((γ⁻¹ * g * γ).1 *ᵥ x) = g.1 *ᵥ (γ.1 *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  simp only [level, Subgroup.mem_inf]
  refine and_congr ⟨fun h => ?_, fun h => mul_mem (mul_mem (inv_mem hγ) h) hγ⟩ ⟨fun hg y => ?_, fun hg x => ?_⟩
  · have := mul_mem (mul_mem hγ h) (inv_mem hγ)
    simpa [mul_assoc] using this
  · have e' : γ.1 *ᵥ ((γ⁻¹).1 *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have := hg ((γ⁻¹).1 *ᵥ y)
    rwa [h, h, e, e'] at this
  · rw [h, h, e]
    exact hg _

end Frames

section Places

variable {F : Type} [Field F] [NumberField F]

theorem card_residue (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) =
      Nat.card (𝓞 F ⧸ v.asIdeal) :=
  (Formalism.UG.P.tjcosets_card_residue v).trans rfl

theorem finite_over {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  simpa [Ideal.dvd_span_singleton] using Ideal.finite_factors h

theorem not_mem_both {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  obtain ⟨a, b, e⟩ : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  exact (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top (e ▸ add_mem (Ideal.mul_mem_left _ _ h1)
    (Ideal.mul_mem_left _ _ h2))

theorem prod_over {p : ℕ} (hp : p.Prime) {f : ℕ}
    (hf : Nat.card {v : HeightOneSpectrum (𝓞 F) // (p : 𝓞 F) ∈ v.asIdeal} = f)
    (a : HeightOneSpectrum (𝓞 F) → ℕ) (c : ℝ) (h : ∀ v, (p : 𝓞 F) ∈ v.asIdeal → (a v : ℝ) = c) :
    ∏ v ∈ (finite_over (F := F) hp).toFinset, (a v : ℝ) = c ^ f := by
  rw [Finset.prod_congr rfl fun v hv => h v (by simpa using hv), Finset.prod_const, ← hf]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset (finite_over hp)).symm

theorem congPre_le {O K : Type} [CommRing O] [CommRing K] (ι : O →+* K) (I : Ideal O) {n : ℕ}
    (H : Subgroup (GL (Fin n) (O ⧸ I))) : congPre ι I H ≤ (bc (n := Fin n) ι).range :=
  Subgroup.map_le_range _ _

end Places

section Record

open GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (sp : Spaces R F E)

def HasFrames (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  ∀ v : HeightOneSpectrum (𝓞 F), ∃ b : GL (Fin R.k) (E ⊗[F] v.adicCompletion F),
    cT (Formalism.UG.sigR sp.cm.sig (v.adicCompletion F)) b.1 * sp.gram0.map (inclE (F := F) (v.adicCompletion F)) * b.1 = 1 ∧
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v

variable {sp}

theorem relIndex_selfDual {N N' : Submodule (𝓞 E) (Fin R.k → E)}
    (hN : HasFrames sp N)
    (hN' : HasFrames sp N')
    (v : HeightOneSpectrum (𝓞 F))
    {U : Subgroup (GL (Fin R.k) (E ⊗[F] v.adicCompletion F))}
    (h : U ≤ levelVL sp.cm.sig sp.gram0 v N) (h' : U ≤ levelVL sp.cm.sig sp.gram0 v N') :
    U.relIndex (levelVL sp.cm.sig sp.gram0 v N) = U.relIndex (levelVL sp.cm.sig sp.gram0 v N') := by
  obtain ⟨b, hb, hbN⟩ := hN.2.2 v
  obtain ⟨b', hb', hbN'⟩ := hN'.2.2 v
  have hγ := mul_inv_mem_UJ hb hb'
  have e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj (b' * b⁻¹)).toMonoidHom =
      levelVL sp.cm.sig sp.gram0 v N' := map_conj_level hγ fun x => by
    rw [hbN, hbN', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
  have hu := GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1
    hN.2.1 v _ hγ
  rw [e] at hu
  exact relIndex_eq_of_symm hu h h'

variable {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)

theorem relIndex_at_g {N : Submodule (𝓞 E) (Fin R.k → E)}
    (hN : HasFrames sp N) (i : Fin 2)
    (hp : (gp i).Prime) (v : HeightOneSpectrum (𝓞 F)) (hs : Nat.card (𝓞 F ⧸ v.asIdeal) = gp i)
    (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    (h : L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) :
    (((L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) : ℕ) : ℝ) =
      idxColLoc (gp i) R.k := by
  obtain ⟨b, hb, hbN⟩ := hN.2.2 v
  have hsw := L.splitG_sig i v hv
  have hint := GlobalTheory.mem_intV_iff_of_splitting _ _ sp.cm v (GlobalTheory.ringEquiv_adicCompletion_mem_integers_iff _ v) _ hsw
  have hlev := GlobalTheory.split_stabGL_iff_mem_range _ _ _ _ _ _ hsw hint _ _ b _ hb hbN
  have hfr := L.Uloc_g i v hv
  have hex := GlobalTheory.OverCompare.existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit sp) _ _ hsw
  generalize bc (n := Fin R.k) ((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom) = p at hlev hfr hex
  have hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y := fun y => by
    obtain ⟨g, hg, -⟩ := hex y
    exact ⟨g.1, g.2, hg⟩
  have hK : levelVL sp.cm.sig sp.gram0 v N =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (p b)
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    ext g
    rw [mem_pull]
    exact and_congr_right fun hg => hlev g hg
  have hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p
      (L.frG i v hv) (iwU F R.k v) := by
    ext g
    rw [mem_pull]
    exact ⟨fun hg => ⟨L.Uloc_le v hg, (hfr g (L.Uloc_le v hg)).1 hg⟩, fun hg => (hfr g hg.1).2 hg.2⟩
  obtain ⟨γ, hγ, eγ⟩ := hsur (L.frG i v hv * (p b)⁻¹)
  have hu := GlobalTheory.StabConjIndex.relIndex_conj_levelVL _ _ sp.cm _ _ sp.baseGram_isHermitian (GlobalTheory.OverCompare.gram_matrix_det_unit sp) N hN.1
    hN.2.1 v _ hγ
  have e : (levelVL sp.cm.sig sp.gram0 v N).map (MulAut.conj γ).toMonoidHom =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p (L.frG i v hv)
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    rw [hK, map_conj_pull _ _ _ hγ, eγ, inv_mul_cancel_right]
  rw [e] at hu
  rw [relIndex_eq_of_symm hu h (hU ▸ pull_mono _ _ _ (congPre_le _ _ _)), hU, relIndex_pull hsur, iwU,
    GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]
  exact GlobalTheory.UniIndexPrime.index_upperUni _ _ _ hp ((card_residue v).trans hs)

theorem local_level_relIndex_at_level_prime_selfDual {N : Submodule (𝓞 E) (Fin R.k → E)}
    (v : HeightOneSpectrum (𝓞 F)) (hs : Nat.card (𝓞 F ⧸ v.asIdeal) = A.T)
    (hv : (A.T : 𝓞 F) ∈ v.asIdeal) {φ} (h : LocalAtT L N v hv φ) :
    (((L.Uloc v).relIndex (levelVL sp.cm.sig sp.gram0 v N) : ℕ) : ℝ) =
      (A.T : ℝ) ^ R.k - 1 := by
  obtain ⟨-, -, -, -, -, hex, -, ⟨b, hb, hlev⟩, f, -, -, -, hf, -, -, hUf⟩ := h
  have hb' : GlobalTheory.OverCompare.IsFrame (partOf (prP φ) (locLat v N)) b := hb
  obtain ⟨r, hr⟩ := hb'.exists_row f
  have hst := hr.mem_stabFun_iff hb'
  generalize bc (n := Fin R.k) (prP φ) = p at hlev hst hex hUf
  have hsur : ∀ y, ∃ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), p g = y := fun y => by
    obtain ⟨g, hg, -⟩ := hex y
    exact ⟨g.1, g.2, hg⟩
  have hK : levelVL sp.cm.sig sp.gram0 v N =
      pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    ext g
    rw [mem_pull]
    exact ⟨fun hg => ⟨hg.1, (hlev g hg.1).1 hg⟩, fun hg => (hlev g hg.1).2 hg.2⟩
  have hU : L.Uloc v = pull (UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) p b
      (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
        (IsLocalRing.maximalIdeal _) (GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm.stabRow r)) := by
    ext g
    rw [mem_pull, hUf, hst]
    exact ⟨fun hg => ⟨hg.1.1, hg.2⟩, fun hg => ⟨(hlev g hg.1).2 (congPre_le _ _ _ hg.2), hg.2⟩⟩
  rw [hK, hU, relIndex_pull hsur, GlobalTheory.CongIndex.relIndex_congPre _ _ _ (FaithfulSMul.algebraMap_injective _ _)]
  exact GlobalTheory.Proof.StabilizerIndex.index_stabRow _ _ _ A.T_prime ((card_residue v).trans hs) r
    ((hr.ne_zero_iff hb').1 hf)

theorem exists_glue (v : HeightOneSpectrum (𝓞 F))
    (x : GL (Fin R.k) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) :
    ∃ g ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F),
      bc (prV (E := E) v) g = x ∧ ∀ w, w ≠ v → bc (prV (E := E) w) g = 1 := by
  refine ⟨Formalism.UG.P.afsplitU v x 1, Formalism.UG.P.afsplitU_mem v _ _ _ _ hx (one_mem _),
    Formalism.UG.P.afsplit_right1 v _ _, fun w hw => ?_⟩
  rw [← map_one (bc (n := Fin R.k) (prV (E := E) w))]
  apply Units.ext
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
    Formalism.UG.P.afsplitC_prV_ne v w hw]

theorem relIndex_level (hp : ∀ i, (gp i).Prime) (hne : gp 0 ≠ gp 1) {f : ℕ}
    (hg : ∀ i, Nat.card {v : HeightOneSpectrum (𝓞 F) // (gp i : 𝓞 F) ∈ v.asIdeal} = f ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (gp i : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = gp i)
    (hT : Nat.card {v : HeightOneSpectrum (𝓞 F) // (A.T : 𝓞 F) ∈ v.asIdeal} = f ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = A.T)
    (hfr : ∀ N, IsSelfDualLat (sp.cm.sig : E →+* E) sp.gram0 N → HasFrames sp N)
    (H : HasOverLattice L) {N : Submodule (𝓞 E) (Fin R.k → E)}
    (hN₁ : IsSelfDualLat (sp.cm.sig : E →+* E) sp.gram0 N) (hUK : L.U ≤ levelAfL sp.cm.sig sp.gram0 N) :
    ((L.U.relIndex (levelAfL sp.cm.sig sp.gram0 N) : ℕ) : ℝ) =
      idxColLoc (gp 0) R.k ^ f * idxColLoc (gp 1) R.k ^ f * ((A.T : ℝ) ^ R.k - 1) ^ f := by
  classical
  obtain ⟨hTg, N₀, hN₀, hloc, hle₀, -⟩ := H
  have hN := hfr N hN₁
  have hN₀' := hfr N₀ ⟨hN₀.1, hN₀.2.1, hN₀.2.2.1⟩
  have hK := GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ sp.cm.sig _ sp.gram0 N hN.1
  have hle : ∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N := fun v x hx => by
    obtain ⟨g, hg, e, h1⟩ := exists_glue v x (L.Uloc_le v hx)
    have hgU : g ∈ L.U := (L.U_eq g).2 ⟨hg, fun w => by
      by_cases hw : w = v
      · subst hw; rwa [e]
      · rw [h1 w hw]; exact one_mem _⟩
    exact e ▸ ((hK g).1 (hUK hgU)).2 v
  have hT' := A.T_prime
  have hidx := GlobalTheory.relIndex_eq_prod_local _ _ _ (fun v => bc (n := Fin R.k) (prV (E := E) v)) _
    (levelAfL sp.cm.sig sp.gram0 N) L.U (fun v => levelVL sp.cm.sig sp.gram0 v N) L.Uloc
    (((finite_over (hp 0)).toFinset ∪ (finite_over (hp 1)).toFinset) ∪ (finite_over hT').toFinset)
    (fun v x hx => exists_glue v x hx.1) hK L.U_eq (fun v hv => by
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hv
      have e : L.Uloc v = levelVL sp.cm.sig sp.gram0 v N₀ := by
        rw [L.Uloc_hyp v hv.1.1 hv.1.2 hv.2]
        exact congrArg (level _ _) (hN₀.2.2.2.2.2 v hv.2).symm
      rw [← Subgroup.relIndex_eq_one, relIndex_selfDual hN hN₀' v (hle v) (hle₀ v), e,
        Subgroup.relIndex_self])
  rw [hidx, Nat.cast_prod, Finset.prod_union, Finset.prod_union,
    prod_over (hp 0) (hg 0).1 _ _ fun v hv => relIndex_at_g L hN 0 (hp 0) v ((hg 0).2 v hv) hv (hle v),
    prod_over (hp 1) (hg 1).1 _ _ fun v hv => relIndex_at_g L hN 1 (hp 1) v ((hg 1).2 v hv) hv (hle v),
    prod_over hT' hT.1 _ ((A.T : ℝ) ^ R.k - 1) fun v hv => by
      obtain ⟨φ, hφ⟩ := hloc v hv
      rw [relIndex_selfDual hN hN₀' v (hle v) (hle₀ v)]
      exact local_level_relIndex_at_level_prime_selfDual L v (hT.2 v hv) hv hφ]
  · rw [Finset.disjoint_left]
    intro v h0 h1
    exact not_mem_both (hp 0) (hp 1) hne v (by simpa using h0) (by simpa using h1)
  · rw [Finset.disjoint_left]
    intro v h0 h1
    rcases Finset.mem_union.1 h0 with h | h
    · exact not_mem_both hT' (hp 0) (hTg 0) v (by simpa using h1) (by simpa using h)
    · exact not_mem_both hT' (hp 1) (hTg 1) v (by simpa using h1) (by simpa using h)

end Record

open GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection in

theorem indexKU_of_selfDualOverBase (H : SelfDualOverBase) : IndexKU := by
  intro D Lv u
  letI := D.host.cmStar
  intro hg hT N hN hUK
  exact relIndex_level (Lv u) D.host.g_prime D.host.g_ne hg hT
    (fun N hN => ⟨hN.1, hN.2.1, fun v => GlobalTheory.SelfDualFrame.exists_frame D N v hN⟩) (H D Lv u hT) hN hUK

end GlobalTheory.LevelIndex
end
end

section
section
namespace GlobalTheory.LevelIndex

theorem selfDualLatticeIndex_stabiliserLevelIndexFormula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel.indexKU_iff.mp
    (GlobalTheory.LevelIndex.indexKU_of_selfDualOverBase
      (GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice))

end GlobalTheory.LevelIndex
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula := by
  atlas_forward_decl GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula
end
