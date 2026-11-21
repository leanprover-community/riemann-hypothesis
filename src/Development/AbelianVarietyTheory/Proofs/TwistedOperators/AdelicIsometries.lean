import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLOfIsVecBasisAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSpacesIsometricOfRankSignature
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer

section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D := by
  first | exact @GlobalTheory.RationalIsometry.rationalSt | exact GlobalTheory.RationalIsometry.rationalSt | (intros; apply GlobalTheory.RationalIsometry.rationalSt <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

def sumMap (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) →ₗ[D.host.E] Y.V :=
  ι.coprod ((Fintype.linearCombination D.host.E z).coprod
    ((Fintype.linearCombination D.host.E e).coprod (Fintype.linearCombination D.host.E f)))

theorem sumMap_apply (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (p : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    sumMap Y X ι z e f p = ι p.1 + (∑ i, p.2.1 i • z i + (∑ i, p.2.2.1 i • e i + ∑ i, p.2.2.2 i • f i)) := by
  simp [sumMap, Fintype.linearCombination_apply]

theorem hT_swap (Y : HSp D) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

theorem form_sumMap {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f)
    (p q : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    Y.hT (sumMap Y X ι z e f p) (sumMap Y X ι z e f q) =
      X.hT p.1 q.1 + (∑ i, star (p.2.1 i) * q.2.1 i * c +
        (∑ i, star (p.2.2.1 i) * q.2.2.2 i + ∑ i, star (p.2.2.2 i) * q.2.2.1 i)) := by
  have hsub : Subsingleton (Fin a) := by
    have := h.a_le
    exact ⟨fun i j => Fin.ext (by omega)⟩
  have zz : ∀ i j, Y.hT (z i) (z j) = if i = j then c else 0 := fun i j => by
    obtain rfl := Subsingleton.elim i j
    rw [if_pos rfl]; exact h.z_norm i
  have zx : ∀ i x, Y.hT (z i) (ι x) = 0 := fun i x => h.z_X i x
  have xz : ∀ i x, Y.hT (ι x) (z i) = 0 := fun i x => by rw [hT_swap, zx, star_zero]
  have ex : ∀ i x, Y.hT (e i) (ι x) = 0 := fun i x => (h.hyp_X i x).1
  have xe : ∀ i x, Y.hT (ι x) (e i) = 0 := fun i x => by rw [hT_swap, ex, star_zero]
  have fx : ∀ i x, Y.hT (f i) (ι x) = 0 := fun i x => (h.hyp_X i x).2
  have xf : ∀ i x, Y.hT (ι x) (f i) = 0 := fun i x => by rw [hT_swap, fx, star_zero]
  have ez : ∀ i j, Y.hT (e i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).1
  have ze : ∀ i j, Y.hT (z j) (e i) = 0 := fun i x => by rw [hT_swap, ez, star_zero]
  have fz : ∀ i j, Y.hT (f i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).2
  have zf : ∀ i j, Y.hT (z j) (f i) = 0 := fun i x => by rw [hT_swap, fz, star_zero]
  have ee : ∀ i j, Y.hT (e i) (e j) = 0 := fun i j => h.ee j i
  have ff : ∀ i j, Y.hT (f i) (f j) = 0 := fun i j => h.ff j i
  have fe : ∀ i j, Y.hT (f i) (e j) = if j = i then 1 else 0 := fun i j => h.ef j i
  have ef : ∀ i j, Y.hT (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hT_swap, fe]; split_ifs <;> simp
  have xx : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := h.isom
  rw [sumMap_apply, sumMap_apply]
  simp only [map_add, map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, zz, zx, xz, ex, xe, fx, xf, ez, ze, fz, zf, ee, ff, fe, ef, xx, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one, RingHom.id_apply, starRingEnd_apply]
  rw [add_comm (∑ i, star (p.2.2.1 i) * q.2.2.2 i)]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem sumMap_injective {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) : Function.Injective (sumMap Y X ι z e f) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, α, β, γ⟩ hp
  have H := fun q => form_sumMap h (x, α, β, γ) q
  simp only [hp, map_zero, LinearMap.zero_apply] at H
  have h1 : x = 0 := X.nondeg.1 x fun y => by simpa using (H (y, 0, 0, 0)).symm
  have h2 : α = 0 := funext fun i => by
    simpa [Pi.single_apply, hc] using (H (0, Pi.single i 1, 0, 0)).symm
  have h3 : β = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, 0, Pi.single i 1)).symm
  have h4 : γ = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, Pi.single i 1, 0)).symm
  simp [h1, h2, h3, h4]

def sumEquiv {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) ≃ₗ[D.host.E] Y.V :=
  LinearEquiv.ofInjectiveOfFinrankEq (sumMap Y X ι z e f) (sumMap_injective h hc) (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, X.rank_eq, Y.rank_eq, h.rank]
    ring)

theorem sumEquiv_apply {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) (p) :
    sumEquiv h hc p = sumMap Y X ι z e f p := rfl

theorem exists_isom {Y Y' X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {ι' : X.V →ₗ[D.host.E] Y'.V} {a ρ : ℕ}
    {z : Fin a → Y.V} {z' : Fin a → Y'.V} {c : D.host.E} {e f : Fin ρ → Y.V} {e' f' : Fin ρ → Y'.V}
    (h : IsDec Y X ι z c e f) (h' : IsDec Y' X ι' z' c e' f') (hc : c ≠ 0) :
    ∃ io : Y.V ≃ₗ[D.host.E] Y'.V, HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' x) ∧ (∀ i, io (z i) = z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i := by
  have key : ∀ p, ((sumEquiv h hc).symm.trans (sumEquiv h' hc)) (sumMap Y X ι z e f p) =
      sumMap Y' X ι' z' e' f' p := fun p => by
    rw [← sumEquiv_apply h hc, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sumEquiv_apply]
  refine ⟨(sumEquiv h hc).symm.trans (sumEquiv h' hc), fun x y => ?_, fun x => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨p, rfl⟩ := (sumEquiv h hc).surjective x
    obtain ⟨q, rfl⟩ := (sumEquiv h hc).surjective y
    rw [sumEquiv_apply, sumEquiv_apply, LinearEquiv.coe_coe, key, key, form_sumMap h, form_sumMap h']
  · simpa [sumMap_apply] using key (x, 0, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, Pi.single i 1, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, Pi.single i 1, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, 0, Pi.single i 1)

theorem isDec_rescale {Y X X' : HSp D} {ι : X'.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X' ι z c e f) (φ : X.V →ₗ[D.host.E] X'.V) (hφ : HSpace.IsIsomEmb X X' φ)
    (hr : X.rank = X'.rank) (π : D.host.E) :
    IsDec Y X (ι ∘ₗ φ) (fun i => π • z i) (c * (π * star π)) e f where
  isom x y := (h.isom _ _).trans (hφ x y)
  a_le := h.a_le
  rank := by rw [hr, h.rank]
  z_norm i := by
    have := h.z_norm i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at this ⊢
    rw [this]; ring
  z_X i x := by
    have := h.z_X i (φ x)
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at this ⊢
    rw [this, mul_zero]
  ee := h.ee
  ff := h.ff
  ef := h.ef
  hyp_X i x := h.hyp_X i (φ x)
  hyperbolicDecomp_hyp_orthogonal_line i j := by
    have := h.hyperbolicDecomp_hyp_orthogonal_line i j
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, smul_eq_mul] at this ⊢
    rw [this.1, this.2, mul_zero]; exact ⟨rfl, rfl⟩

theorem stdIsomSt_of_rationalSt : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  intro D hR u
  refine ⟨?_, ?_⟩
  · obtain ⟨π, h1, h2, -⟩ := D.T_norm u
    exact ⟨π, h1, by rw [bridge_star_holds D.R D.host]; exact h2⟩
  intro π hπ s a ρ Y X ι z e f Y' X' ι' z' e' f' h h' hX hX' hp hp' hr
  obtain ⟨φ, hφ⟩ := hR X X' hX hX' hr fun τ => by rw [hp τ, hp' τ, hr]
  have h2 := isDec_rescale h' φ.toLinearMap hφ hr (π : D.host.E)
  rw [hπ.2] at h2
  have hc : ((s : ℤ) : D.host.E) * Tu D u ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr s.ne_zero) (Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero)
  obtain ⟨io, a1, a2, a3, a4⟩ := exists_isom h h2 hc
  exact ⟨φ, io, hφ, a1, a2, a3, a4⟩

end GlobalTheory.StdIsom
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  atlas_forward_decl GlobalTheory.StdIsom.stdIsomSt_of_rationalSt
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  atlas_forward_decl GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  first | exact @GlobalTheory.HypLattice.isSelfDualC_lamN | exact GlobalTheory.HypLattice.isSelfDualC_lamN | (intros; apply GlobalTheory.HypLattice.isSelfDualC_lamN <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  atlas_forward_decl GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal
end

section
namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, h1⟩ := h1
    obtain ⟨c2, hc2, h2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add, mul_comm c1 c2, mul_smul, mul_comm c2 c1, mul_smul]
    exact L.add_mem (L.smul_mem c2 h1) (L.smul_mem c1 h2)
  | smul a x _ h =>
    obtain ⟨c0, hc0, h0⟩ := h
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨c0 * (s : RingOfIntegers E), mul_ne_zero hc0 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have key : (s : RingOfIntegers E) • (a • x) = b • x := by
      rw [← algebraMap_smul E (s : RingOfIntegers E), smul_smul, mul_comm, hs, algebraMap_smul]
    rw [mul_smul, key, smul_comm c0 b x]
    exact L.smul_mem b h0

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add, map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  refine ⟨GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
    exact Submodule.map_comap_le _ _
  · rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc, hx⟩ := exists_smul_mem L (y := ι x) (hsp ▸ Submodule.mem_sup_left ⟨x, rfl⟩)
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E c ≠ 0 := by simpa using hc
    have : x = (algebraMap (𝓞 D.host.E) D.host.E c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul D.host.E c, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    change (ι.restrictScalars (𝓞 D.host.E)) (c • x) ∈ L
    rw [map_smul]
    exact hx
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add, map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  atlas_forward_decl GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.GlueBase

open GlobalTheory.IdemSupport (cP)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem split_prime {e a t t' : A} (ht : t' * t = 1) {y f : M} (hy : e • y = y) :
    y = e • (y - a • f) + (a * (e * t')) • (t • f) := by
  have key : a * (e * t') * t = e * a := by linear_combination (a * e) * ht
  rw [smul_sub, hy, smul_smul, smul_smul, key, sub_add_cancel]

theorem mem_of_mul_sub (S : Subring A) {b h t : A} (hb : b ∈ S) (h1 : b * h ∈ S) (h2 : h - t ∈ S) : b * t ∈ S := by
  have hd := S.sub_mem h1 (S.mul_mem hb h2)
  rwa [mul_sub, sub_sub_cancel] at hd

theorem mem_of_sub (S : Subring A) {a b : A} (ha : a ∈ S) (h : a - b ∈ S) : b ∈ S := by
  have hd := S.sub_mem ha h
  rwa [sub_sub_cancel] at hd

theorem idem_smul_smul {e : A} (he : e * e = e) (x : M) : e • e • x = e • x := by
  rw [smul_smul, he]

end Alg

variable {D : D7}

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (Tu_ne_zero u), map_one]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc]
  congr 1
  simp [Tu, star_inv₀]

theorem hA_idem {X : HSp D} {e : EAf D} {y : Fin X.rank → EAf D} (hy : cjA D e • y = y) (x : Fin X.rank → EAf D) :
    hA X x y = hA X (e • x) y := by
  conv_lhs => rw [← hy]
  rw [hA_smul_right, hA_smul_left, cjA_cjA]

theorem isBasePair_of_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f : Fin X.rank → EAf D) (hL : Submodule.IsLattice D.host.E L₀) (hf : IsGlueVec X u L₀ f) :
    IsBasePair X u π L₀ fun w => idem w • f := by
  have ht : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := inc_inv_mul u
  unfold IsBasePair
  refine ⟨hL, fun w e he hT y => ?_, fun w e he hπw => ?_⟩
  ·
    obtain rfl := eq_idem he
    have hinv : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hT
    simp only [InCmp]
    constructor
    · rintro ⟨hy, hey⟩
      exact ⟨(mem_hat_dualL_iff hL y).2 fun x hx => hf.int x hx y hy, hey⟩
    · rintro ⟨hy, hey⟩
      obtain ⟨a, ha, hya⟩ := hf.dual y ((mem_hat_dualL_iff hL y).1 hy)
      refine ⟨?_, hey⟩
      rw [split_prime (a := a) (f := f) ht hey]
      exact add_mem_hat (smul_mem_hat (idem_mem w) hya) (smul_mem_hat ((OA D).mul_mem ha hinv) hf.mul_mem)
  ·
    obtain rfl := eq_idem he
    have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← pi_mul_cO hπ]
      exact w.asIdeal.mul_mem_right _ hπw
    have hnot : idem w * inc D (Tu D u)⁻¹ ∉ OA D := fun h => (idem_mul_inv_mem_iff u w).1 h hTw
    have hff : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D := hf.norm
    refine ⟨idem_smul_smul (idem_mul_self w) f, ?_, ?_, ?_⟩
    · show inc D (Tu D u) • (idem w • f) ∈ hat L₀
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_hat (idem_mem w) hf.mul_mem
    ·
      intro hmem
      apply hnot
      refine mem_of_mul_sub (OA D) (idem_mem w) ?_ hff
      rw [← hA_smul_left, ← cjA_hA]
      exact cjA_mem (hf.pair _ hmem)
    · intro y
      simp only [InCmp]
      constructor
      · rintro ⟨hy, hey⟩
        refine ⟨hey, fun x hx => hf.int x hx.1 y hy, ?_⟩
        rw [hA_smul_left]
        exact (OA D).mul_mem (idem_mem w) (hf.pair y hy)
      · rintro ⟨hey, hx, hfy⟩
        have hdual : ∀ x ∈ hat L₀, hA X x y ∈ OA D := by
          intro x hx'
          rw [hA_idem hey]
          exact hx _ ⟨smul_mem_hat (idem_mem w) hx', idem_smul_smul (idem_mul_self w) x⟩
        obtain ⟨a, ha, hya⟩ := hf.dual y hdual
        refine ⟨?_, hey⟩
        have h1 : cjA D a * idem w * hA X f f ∈ OA D := by
          have hp : hA X (idem w • f) (a • f) ∈ OA D := by
            refine mem_of_sub (OA D) hfy ?_
            rw [← hA_sub_right, hA_smul_left]
            exact (OA D).mul_mem (idem_mem w) (hf.pair _ hya)
          rwa [hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (idem w)] at hp
        have h2 : cjA D a * idem w * inc D (Tu D u)⁻¹ ∈ OA D :=
          mem_of_mul_sub (OA D) ((OA D).mul_mem (cjA_mem ha) (idem_mem w)) h1 hff
        have h3 : a * (cjA D (idem w) * inc D (Tu D u)⁻¹) ∈ OA D := by
          have hc := cjA_mem h2
          rwa [map_mul, map_mul, cjA_cjA, cjA_inc_inv, mul_assoc] at hc
        rw [split_prime (a := a) (f := f) ht hey]
        exact add_mem_hat (smul_mem_hat (cjA_mem (idem_mem w)) hya) (smul_mem_hat h3 hf.mul_mem)

end GlobalTheory.AdIsom.GlueBase
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f : Fin X.rank → EAf D), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ f → IsBasePair X u π L₀ fun w => idem w • f := by
  atlas_forward_decl GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_proj {K M : Type} [Field K] [AddCommGroup M] [Module K M] (U : Submodule K M) :
    ∃ Q : M →ₗ[K] M, (∀ x ∈ U, Q x = 0) ∧ ∀ x, x - Q x ∈ U := by
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨LinearMap.id - U.subtype ∘ₗ U.projectionOnto W hW, fun x hx => ?_, fun x => ?_⟩
  · have := Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩
    simp [this]
  · simp

theorem exists_lattice {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (Λ : Submodule O (Fin n → K))
    (h : Λ.FG) : ∃ (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (Λ' : Submodule O (Fin n → K)),
      Submodule.IsLattice K Λ' ∧ Λ ≤ Λ' ∧ (∀ x ∈ Λ, Q x = 0) ∧ ∀ x ∈ Λ', Q x = 0 → x ∈ Λ := by
  obtain ⟨Q, h1, h2⟩ := exists_proj (Submodule.span K (Λ : Set (Fin n → K)))
  have h3 : ∀ x, Q (Q x) = Q x := fun x => by
    have := h1 _ (h2 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨Q, Λ ⊔ Submodule.span O (Set.range fun j : Fin n => Q (Pi.single j 1)), ⟨?_, ?_⟩, le_sup_left,
    fun x hx => h1 x (Submodule.subset_span hx), fun x hx h0 => ?_⟩
  · exact h.sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, ← sub_add_cancel (Pi.single j 1 : Fin n → K) (Q (Pi.single j 1))]
    refine add_mem (Submodule.span_mono ?_ (h2 _)) (Submodule.subset_span ?_)
    · exact fun y hy => Submodule.mem_sup_left hy
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h4 : Q b = b := by
      refine Submodule.span_induction (p := fun b _ => Q b = b) ?_ (map_zero Q) ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        exact h3 _
      · intro x y _ _ hx hy
        rw [map_add, hx, hy]
      · intro c x _ hx
        rw [← algebraMap_smul K c x, map_smul, hx]
    rw [map_add, h1 a (Submodule.subset_span ha), h4, zero_add] at h0
    rwa [h0, add_zero]

theorem map_mulVec_gen {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) {n : ℕ}
    (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (LinearMap.toMatrix' Q).map f *ᵥ (fun i => f (x i)) = fun i => f (Q x i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec, RingHom.map_mulVec]
  rfl

variable {D : D7}

theorem inc_injective : Function.Injective (inc D) := by
  obtain ⟨P, hP, h0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField D.host.E) |>.imp fun _ h => h.symm
  intro a b hab
  have := congrArg (GlobalTheory.StdFrames.cpt (D := D) ⟨P, hP.isPrime, h0⟩) hab
  rw [cpt_inc, cpt_inc] at this
  exact (algebraMap D.host.E _).injective this

theorem mem_of_inc_mem_hat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    {x : Fin n → D.host.E} (hx : (fun i => inc D (x i)) ∈ hat Λ) : x ∈ Λ := by
  obtain ⟨Q, Λ', h1, h2, h3, h4⟩ := exists_lattice Λ h
  refine h4 x ((inc_mem_hat_iff h1 x).1 (hat_mono h2 hx)) ?_
  have h5 : (LinearMap.toMatrix' Q).map (inc D) *ᵥ (fun i => inc D (x i)) = 0 := by
    refine hat_induction (p := fun y => (LinearMap.toMatrix' Q).map (inc D) *ᵥ y = 0) ?_ (mulVec_zero _) ?_ ?_ hx
    · intro y hy
      rw [map_mulVec_gen, h3 y hy]
      funext i
      exact RingHom.map_zero _
    · intro a b ha hb
      rw [mulVec_add, ha, hb, add_zero]
    · intro a _ b hb
      rw [mulVec_smul, hb, smul_zero]
  rw [map_mulVec_gen] at h5
  funext i
  exact inc_injective ((congrFun h5 i).trans (RingHom.map_zero _).symm)

theorem inCmp_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y L) y ↔ InCmp (idem w) (Formalism.L2.Herm.crdLat Y L') y := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · rcases (T_mem_iff hπ w).1 hT with hw | hw
    · exact ((h.2.2 w _ (isPlIdem_idem w) hw).1 y).trans ((h'.2.2 w _ (isPlIdem_idem w) hw).1 y).symm
    · have a := h.2.2 _ _ (isPlIdem_idem _) hw
      have a' := h'.2.2 _ _ (isPlIdem_idem _) hw
      rw [cjA_idem, GlobalTheory.StdFrames.cP_cP] at a a'
      refine (a.2 y).trans (Iff.trans ?_ (a'.2 y).symm)
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y' => ?_
      rw [a.1 y', a'.1 y']
  · exact (h.2.1 w _ (isPlIdem_idem w) hT y).trans (h'.2.1 w _ (isPlIdem_idem w) hT y).symm

theorem glued_le {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') : L ≤ L' := by
  intro x hx
  have hfg : (Formalism.L2.Herm.crdLat Y L').FG := h'.1.map _
  have h1 : vA Y x ∈ hat (Formalism.L2.Herm.crdLat Y L') := mem_hat_of_idem hfg fun w =>
    ((inCmp_iff hπ h h' w _).1 ⟨smul_mem_hat (idem_mem w) (vA_mem_hat Y hx), by rw [smul_smul, idem_mul_self]⟩).1
  obtain ⟨x', hx', e⟩ := mem_of_inc_mem_hat hfg h1
  rwa [← (Formalism.L2.Herm.crd Y).injective e]

theorem glued_unique (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (Y X : HSp D)
    (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L L' : Submodule (𝓞 D.host.E) Y.V) (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') :
    L = L' :=
  le_antisymm (glued_le hπ h h') (glued_le hπ h' h)

end GlobalTheory.GlueUnique

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedHermitianLattice_unique : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) (L L' : Submodule (𝓞 D.host.E) Y.V), IsGlued Y X ι z u π L₀ f₀ L → IsGlued Y X ι z u π L₀ f₀ L' → L = L' := by
  atlas_forward_decl GlobalTheory.GlueUnique.glued_unique
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_eq_iff_idempotent_components_over : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  first | exact @GlobalTheory.LocHat.locL_eq_iff_idem | exact GlobalTheory.LocHat.locL_eq_iff_idem | (intros; apply GlobalTheory.LocHat.locL_eq_iff_idem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_image_adelicUnitary : ∀ D : D7, ImageSt D := by
  first | exact @GlobalTheory.AdIsomImage.imageSt | exact GlobalTheory.AdIsomImage.imageSt | (intros; apply GlobalTheory.AdIsomImage.imageSt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  first | exact @GlobalTheory.AdIsomCorrection.correction_of_transport | exact GlobalTheory.AdIsomCorrection.correction_of_transport | (intros; apply GlobalTheory.AdIsomCorrection.correction_of_transport <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.SelfDualGlue

variable {D : D7} {u : D.what₂.Word} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V}

theorem vA_flat (x : X.V) (a : D.host.E) : vA Y (ι x + a • z) = mA Y X ι *ᵥ vA X x + inc D a • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem inc_hD_flat (h : IsLine Y X ι z u) (x x' : X.V) (a a' : D.host.E) :
    inc D (Y.hD (ι x + a • z) (ι x' + a' • z)) =
      hA X (vA X x) (vA X x') - inc D a * cjA D (inc D a') * inc D (Tu D u) := by
  rw [← hA_vA, vA_flat, vA_flat]
  exact hA_flat h _ _ _ _

theorem mem_glueLat_iff {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E,
      y = ι (x + (a : D.host.E) • x₀) + ((a : D.host.E) * (Tu D u)⁻¹) • z := by
  rw [mem_glueLat]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun a => ?_
  rw [map_add, map_smul, smul_add, smul_smul]
  constructor <;> rintro rfl <;> abel

theorem coords_of_mem (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ x : X.V} {a : D.host.E}
    (hm : ι x + a • z ∈ glueLat Y X ι z u L₀ x₀) :
    ∃ x₁ ∈ hat L₀, ∃ b ∈ OA D, vA X x = x₁ + b • vA X x₀ ∧ inc D a = b * inc D (Tu D u)⁻¹ := by
  have hv := vA_mem_hat Y hm
  rw [vA_flat, mem_hat_glueLat] at hv
  obtain ⟨x₁, hx₁, b, hb, e⟩ := hv
  obtain ⟨e1, e2⟩ := flat_inj h e
  exact ⟨x₁, hx₁, b, hb, e1, e2⟩

theorem mem_flatSp (x : X.V) (a : D.host.E) : ι x + a • z ∈ flatSp Y X ι z := Submodule.add_mem_sup (LinearMap.mem_range_self ι x)
    (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self z))

set_option maxHeartbeats 1600000 in

theorem isGlueVec_of_isSDIn : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  obtain ⟨-, -, hsd⟩ := hSD

  have key : ∀ (p : X.V) (α : D.host.E) (q : X.V) (β : D.host.E),
      ι p + α • z ∈ glueLat Y X ι z u L₀ x₀ → ι q + β • z ∈ glueLat Y X ι z u L₀ x₀ →
      hA X (vA X p) (vA X q) - inc D α * cjA D (inc D β) * inc D (Tu D u) ∈ OA D := by
    intro p α q β hp hq
    rw [← inc_hD_flat h, inc_mem_iff]
    exact (hsd _ (mem_flatSp (ι := ι) (z := z) q β)).1 hq _ hp

  have hX : ∀ p : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → ι p + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    intro p hp
    rw [mem_glueLat_iff]
    exact ⟨p, hp, 0, by simp⟩
  have hg : ι x₀ + (Tu D u)⁻¹ • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [mem_glueLat_iff]
    exact ⟨0, by simp, 1, by simp⟩
  have hv : ∀ y : Fin X.rank → D.host.E,
      (fun i => inc D (y i)) = vA X ((Formalism.L2.Herm.crd X).symm y) := by
    intro y
    funext i
    simp [vA]
  have hrat : ∀ p q : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → Formalism.L2.Herm.crd X q ∈ L₀ →
      hA X (vA X p) (vA X q) ∈ OA D := by
    intro p q hp hq
    simpa using key p 0 q 0 (hX p hp) (hX q hq)

  have hright : ∀ f, (∀ y ∈ L₀, hA X f (fun i => inc D (y i)) ∈ OA D) →
      ∀ y ∈ hat L₀, hA X f y ∈ OA D := by
    intro f hf y hy
    refine hat_induction (p := fun y => hA X f y ∈ OA D) hf ?_ ?_ ?_ hy
    · show hA X f 0 ∈ OA D
      rw [hA_zero_right]
      exact zero_mem _
    · intro a b ha hb
      show hA X f (a + b) ∈ OA D
      rw [hA_add_right]
      exact add_mem ha hb
    · intro a ha b hb
      show hA X f (a • b) ∈ OA D
      rw [hA_smul_right]
      exact mul_mem (cjA_mem ha) hb
  have hint : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D := by
    intro x hx
    refine hright x fun y hy => hA_mem_of_forall (fun x' hx' => ?_) x hx
    rw [hv x', hv y]
    exact hrat _ _ (by simpa using hx') (by simpa using hy)

  have hz : ι 0 + (1 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [map_zero, zero_add]
    exact (hP 1).2 (one_mem _)
  obtain ⟨x₁, hx₁, b, -, e1, e2⟩ := coords_of_mem h hz
  have hb : b = inc D (Tu D u) := by
    rw [map_one] at e2
    calc b = b * (inc D (Tu D u)⁻¹ * inc D (Tu D u)) := by rw [inc_inv_mul, mul_one]
      _ = inc D (Tu D u) := by rw [← mul_assoc, ← e2, one_mul]
  have h0 : vA X (0 : X.V) = 0 := by simpa using vA_add X (0 : X.V) 0
  refine ⟨?_, hint, ?_, ?_, ?_⟩
  · rw [h0] at e1
    rw [← hb, eq_sub_of_add_eq' e1.symm]
    exact sub_mem_hat zero_mem_hat hx₁
  · refine hright (vA X x₀) fun y hy => ?_
    rw [hv y]
    simpa using key x₀ (Tu D u)⁻¹ _ 0 hg (hX _ (by simpa using hy))
  · have := key x₀ (Tu D u)⁻¹ x₀ (Tu D u)⁻¹ hg hg
    rwa [cjA_inc_inv, mul_assoc, inc_inv_mul, mul_one] at this
  ·

    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_sub_inc_mem_hat hlat.span_eq_top y
    obtain ⟨q, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y₀
    change y - vA X q ∈ hat L₀ at hy₀
    have hq : ι q + X.hD q x₀ • z ∈ glueLat Y X ι z u L₀ x₀ := by
      refine (hsd _ (mem_flatSp (ι := ι) (z := z) q (X.hD q x₀))).2 fun v hv' => ?_
      obtain ⟨p, hp, a, rfl⟩ := (mem_glueLat_iff v).1 hv'
      have hp' : vA X p ∈ hat L₀ := inc_mem_hat hp
      have h1 : hA X (vA X p) (vA X q) ∈ OA D := by
        rw [show vA X q = y - (y - vA X q) from (sub_sub_cancel y (vA X q)).symm, hA_sub_right]
        exact sub_mem (hy _ hp') (hint _ hp' _ hy₀)
      rw [← inc_mem_iff, inc_hD_flat h, ← hA_vA X q x₀, cjA_hA, vA_add, vA_smul, hA_add_left,
        hA_smul_left, map_mul (inc D)]
      convert h1 using 1
      linear_combination (-(inc D (a : D.host.E) * hA X (vA X x₀) (vA X q))) * inc_inv_mul u
    obtain ⟨x₂, hx₂, c, hc, e3, -⟩ := coords_of_mem h hq
    refine ⟨c, hc, ?_⟩
    have e4 : y - c • vA X x₀ = (y - vA X q) + x₂ := by
      rw [e3]
      abel
    rw [e4]
    exact add_mem_hat hy₀ hx₂

end GlobalTheory.AdIsom.SelfDualGlue
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  atlas_forward_decl GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueVecLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem mem_of_coords {L₀ : Lat X} {x₀ x : X.V} {t : D.host.E}
    (h1 : t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (h2 : Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ := by
  obtain ⟨a, ha⟩ := h1
  refine (mem_glueLat _).2 ⟨_, h2, a, ?_⟩
  change _ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _
  rw [ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]
  abel

theorem coords_of_mem_hat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ x : X.V}
    {t : D.host.E} (hy : vA Y (ι x + t • z) ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀))) :
    t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
      Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ := by
  obtain ⟨x₁, hx₁, a, ha, e⟩ := (mem_hat_glueLat _).1 hy
  rw [vA_flat] at e
  obtain ⟨e1, e2⟩ := flat_inj h e
  have e3 : a = inc D (t * Tu D u) := by
    rw [RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]
  refine ⟨(inc_mem_iff _).1 (e3 ▸ ha), (inc_mem_hat_iff hL _).1 ?_⟩
  change vA X (x - (t * Tu D u) • x₀) ∈ _
  have e4 : vA X (x - (t * Tu D u) • x₀) = x₁ := by
    rw [sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]
  rwa [e4]

theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

theorem mem_flatSp (y : Y.V) : y ∈ flatSp Y X ι z ↔ ∃ (x : X.V) (t : D.host.E), y = ι x + t • z := by
  rw [flatSp, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩

theorem glueLat_fg {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) : (glueLat Y X ι z u L₀ x₀).FG := by
  refine Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)
  have e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
      L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀
      rwa [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hL.fg.map _

theorem span_glueLat {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) = flatSp Y X ι z := by
  have h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) := by
    intro x
    obtain ⟨y, rfl⟩ := (Formalism.L2.Herm.crd X).symm.surjective x
    have hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E)) := hL.span_eq_top ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, -, a, rfl⟩ := (mem_glueLat y).1 hy
    refine (mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩
    rw [map_add, map_smul, smul_add, smul_smul]
    abel
  · obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
    refine add_mem (h1 x) (Submodule.smul_mem _ t ?_)
    have h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) :=
      Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)
    have h3 := Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))
    rwa [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul] at h3

theorem isSDIn_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) := by
  refine ⟨glueLat_fg hL x₀, span_glueLat hL x₀, fun y hy => ?_⟩
  obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
  have key := mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)
  rw [← vA_flat] at key
  constructor
  · intro hm x' hx'
    rw [← inc_mem_iff, ← hA_vA]
    exact key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')
  · intro H
    have h1 := coords_of_mem_hat h hL (key.2 (hA_mem_of_forall ?_))
    · exact mem_of_coords h1.1 h1.2
    · rintro _ ⟨x', hx', rfl⟩
      change hA Y (vA Y x') _ ∈ _
      rw [hA_vA, inc_mem_iff]
      exact H x' hx'

theorem capX_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
      rw [zero_smul, add_zero]; exact hx
    have h2 := ((mem_iff_coords h hL x 0).1 h1).2
    rwa [zero_mul, zero_smul, sub_zero] at h2
  · intro hy
    obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y
    exact ⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩

theorem isPrim_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsPrim Y z (glueLat Y X ι z u L₀ x₀) := by
  intro a
  have e : a • z = ι 0 + a • z := by rw [map_zero, zero_add]
  rw [e, mem_iff_coords h hL, ← inc_mem_hat_iff hL, ← inc_mem_iff, ← inc_mem_iff]
  change _ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _
  rw [zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]
  generalize inc D a = b
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := hg.pair _ h2
    rw [hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu] at h3
    have h4 := mul_mem (cjA_mem h1) hg.norm
    rw [RingHom.map_mul, cjA_inc_Tu] at h4
    rw [← cjA_mem_iff]
    convert neg_mem (add_mem h3 h4) using 1
    linear_combination (-(cjA D b)) * inc_inv_mul u
  · intro hb
    refine ⟨mul_mem hb (inc_Tu_mem u), ?_⟩
    rw [← neg_mul, ← smul_smul]
    exact smul_mem_hat (neg_mem hb) hg.mul_mem

theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL hg, capX_glueLat h hL x₀⟩

end GlobalTheory.GlueVecLattice

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  atlas_forward_decl GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_prescribed_localComponents : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) → IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  atlas_forward_decl GlobalTheory.GluedCmp.isGlued_glueLat
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem transportSt (D : D7) : TransportSt D := by
  intro W Y hr L Λ hL hΛ S hS n be be' h h'
  refine ⟨exists_transport W Y hr L Λ hL hΛ S hS n be be' h h', fun x hx x' => ?_⟩
  exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' hL.1 h x hx x'

theorem gluedSt (D : D7) : GluedSt D := by
  intro u π hπ Y X ι z hz L₀ f₀ hb
  have hL₀ : Submodule.IsLattice D.host.E L₀ := hb.1

  obtain ⟨f, hf, hff⟩ := GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData D u π hπ X L₀ f₀ hb
  obtain ⟨x, hx⟩ := exists_sub_inc_mem_hat (D := D) (Λ := L₀) hL₀.span_eq_top f
  obtain ⟨x₀, hx₀⟩ := vA_surj X x
  rw [← hx₀] at hx
  have hg : IsGlueVec X u L₀ (vA X x₀) := hf.congr hx
  have hgl : IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
    refine GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz L₀ x₀ f₀ hL₀ hg (fun w hw => ⟨?_, ?_⟩)
    · rw [← hff w hw, smul_smul, idem_mul_self]
    · rw [← hff w hw, ← smul_sub]
      exact smul_mem_hat (idem_mem w) hx
  have huniq : ∀ L, IsGlued Y X ι z u π L₀ f₀ L → L = glueLat Y X ι z u L₀ x₀ :=
    fun L hL => GlobalTheory.T.gluedHermitianLattice_unique D u π hπ Y X ι z L₀ f₀ L _ hL hgl
  refine ⟨⟨_, hgl, huniq⟩, fun L hL => ?_⟩
  rw [huniq L hL]
  exact GlobalTheory.T.gluedLattice_selfDual_primitive_meet D u Y X ι z hz L₀ x₀ hL₀ hg

theorem ungluedSt (D : D7) : UngluedSt D := by
  intro u π hπ Y X ι z hz L hSD hP
  obtain ⟨hlat, x₀, hL⟩ := GlobalTheory.T.primitive_lattice_glued_from_intersection D u Y X ι z hz L hSD hP

  have hg : IsGlueVec X u (capX Y X ι L) (vA X x₀) := by
    have key := GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive D u Y X ι z hz (capX Y X ι L) x₀ hlat
    rw [← hL] at key
    exact key hSD hP
  refine ⟨fun w => idem w • vA X x₀, GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector D u π hπ X _ _ hlat hg, ?_⟩
  have key := GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz (capX Y X ι L) x₀ (fun w => idem w • vA X x₀) hlat hg
    (fun w _ => ⟨by simp only [smul_smul, idem_mul_self], by simp only [sub_self]; exact zero_mem_hat⟩)
  rwa [← hL] at key

theorem adelicIsometries (D : D7) : AdelicIsometries D := by
  unfold AdelicIsometries LamNSt
  exact ⟨plIdemSt D, transportSt D, GlobalTheory.T.correctionSt_of_transportSt D (transportSt D),
    splitGlueSt_of D (fun n Λ Λ' hΛ hΛ' v => GlobalTheory.T.localLattice_eq_iff_idempotent_components_over D n Λ Λ' hΛ hΛ' v),
    GlobalTheory.T.selfDualLattice_image_adelicUnitary D, GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D, GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry D (GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D), GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof D,
    gluedSt D, ungluedSt D,
    ⟨fun u Y X ι z ρ e f h L hL nn hn => GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable D u Y X ι z ρ e f h L hL nn hn,
      (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).1, (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).2⟩,
    frameSt D⟩

end GlobalTheory.AdIsom

end
end
