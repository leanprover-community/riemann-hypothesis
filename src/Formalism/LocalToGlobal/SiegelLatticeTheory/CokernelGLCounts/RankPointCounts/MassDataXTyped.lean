import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InclR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol


end Formalism.L2.SG.Pf
end
end

section
noncomputable section

namespace Formalism.L2.SG.LocVol.LJP

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

def DiagProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : PlX X),
    TFv X w v = Matrix.diagonal (fun i : Fin (D.R.rS + 1) =>
      if i = Fin.last D.R.rS then -((Tw w : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) else 0)

def HermProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : PlX X),
    TFv X w v ∈ HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1)

def IntProp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (v : PlX X),
    TypAt X v → (gAt X v : ℤ) ∣ ((Tw u : ℤ) - Tw u') →
      ∀ i j, (TFv X u' v i j - TFv X u v i j) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.LocVol.LJP
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.SG.LocVol.LJP

theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas x) (Formalism.L2.SG.HidaSetting.crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y]
  rfl

theorem diag : DiagProp := by
  intro D X w v
  have hze : ∀ a, (VS D).hT (X.zu w) (X.eX a) = 0 := by
    intro a
    have h := (VS D).herm.eq (X.eX a) (X.zu w)
    rw [(X.zu_orth w a).1] at h
    simpa using h.symm
  ext a b
  simp only [TFv, Matrix.map_apply, Matrix.diagonal_apply, gramE]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, hE_crdOf, X.zu_norm, Tw]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, hze, Ne.symm (Fin.castSucc_ne_last j)]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_last, Fin.snoc_castSucc, hE_crdOf, (X.zu_orth w i).1, Fin.castSucc_ne_last]
    | cast j => simp [Formalism.L2.SG.Sub.F0, TypedSets.frameOf, Fin.snoc_castSucc, hE_crdOf, X.ee, Fin.castSucc_ne_last]

theorem herm : HermProp := by
  intro D X w v
  rw [diag X w v]
  intro a b
  by_cases h : a = b
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem integral : IntProp := by
  intro D X u u' v _ hdiv i j
  rw [diag X u' v, diag X u v]
  by_cases h : i = j ∧ i = Fin.last D.R.rS
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, hk⟩ := hdiv
    simp only [Matrix.diagonal_apply_eq, if_true]
    letI : CharZero (Fv X.B.I.F v) := charZero_of_injective_algebraMap (algebraMap X.B.I.F (Fv X.B.I.F v)).injective
    have hg : ((gAt X v : ℕ) : Fv X.B.I.F v) ≠ 0 := Nat.cast_ne_zero.2 (gAt_prime X v).ne_zero
    have hA : ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
        ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) * (k : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
      have := congrArg (Int.cast : ℤ → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) hk
      push_cast at this
      exact this
    have hs : ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = 1 := by
      rw [show sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ =
          Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (B := X.B.I.E) ((gAt X v : Fv X.B.I.F v))⁻¹ from rfl,
        ← map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := X.B.I.F) (A := Fv X.B.I.F v) (B := X.B.I.E)),
        ← map_mul, mul_inv_cancel₀ hg, map_one]
    have e1 : (-((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) *
        sc (E := X.B.I.E) v ((gAt X v : Fv X.B.I.F v))⁻¹ = inclR (Fv X.B.I.F v) ((k : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [show -((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - -((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) =
          ((Tw u : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) - ((Tw u' : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) by ring,
        hA, mul_comm ((gAt X v : ℕ) : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E), mul_assoc, hs, mul_one]
      simp
    rw [e1]
    unfold OEv
    exact Submodule.subset_span ⟨(k : 𝓞 X.B.I.E), Set.mem_univ _, rfl⟩
  · have h0 : ∀ d : Fin (D.R.rS + 1) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, (∀ l, l ≠ Fin.last D.R.rS → d l = 0) →
        Matrix.diagonal d i j = 0 := by
      intro d hd
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq]; exact hd _ (fun h' => h ⟨rfl, h'⟩)
      · exact Matrix.diagonal_apply_ne _ hij
    rw [h0 _ (fun l hl => if_neg hl), h0 _ (fun l hl => if_neg hl), sub_zero, zero_mul]
    unfold OEv
    exact Submodule.zero_mem _

end Formalism.L2.SG.LocVol.LJP
end

section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

variable {D : D7} (X : HidaSetting D)

theorem sig_ne_id : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
  intro h
  have hall : ∀ a : X.B.I.E, a ∈ (⊥ : Subalgebra X.B.I.F X.B.I.E) := by
    intro a
    have h1 : X.B.I.cm.sig a = a := by rw [h]; rfl
    obtain ⟨c, hc⟩ := (X.B.I.cm.fixed a).1 h1
    exact Algebra.mem_bot.2 ⟨c, hc⟩
  have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := eq_top_iff.2 fun a _ => hall a
  have h1 : Module.finrank X.B.I.F X.B.I.E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  have h2 := X.B.I.cm.deg2
  omega





end Formalism.L2.SG.Pf.MassDataX
end
end

section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX.SDL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

def swp : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem swp_tmul (a : E) (c : Fv F v) : swp v (a ⊗ₜ[F] c) = c ⊗ₜ[F] a := rfl

def swVv (w : Fin n → E ⊗[F] Fv F v) : Fin n → Fv F v ⊗[F] E := fun i => swp v (w i)

theorem swVv_injective : Function.Injective (swVv (E := E) v (n := n)) := fun _ _ h =>
  funext fun i => (swp v).injective (congrFun h i)

theorem swVv_surjective : Function.Surjective (swVv (E := E) v (n := n)) := fun w =>
  ⟨fun i => (swp v).symm (w i), funext fun i => (swp v).apply_symm_apply (w i)⟩

theorem swVv_incl (x : Fin n → E) :
    swVv v (fun i => PI.SelfDualLoc.inclE (F := F) (Fv F v) (x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  simp [swVv, swp, PI.SelfDualLoc.inclE, ratV, inclR, Algebra.TensorProduct.comm_tmul]

theorem sig_swap (σ : E →ₐ[F] E) (t : E ⊗[F] Fv F v) :
    sigR (Fv F v) σ (swp v t) = swp v (PI.SelfDualLoc.sigR σ (Fv F v) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [sigR, PI.SelfDualLoc.sigR, swp, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem incl_swap (e : E) : swp v (PI.SelfDualLoc.inclE (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) e := by
  simp [swp, PI.SelfDualLoc.inclE, inclR, Algebra.TensorProduct.comm_tmul]

theorem hR_swap (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (z y : Fin n → E ⊗[F] Fv F v) :
    hR (Fv F v) σ J (swVv v z) (swVv v y) =
      swp v (PI.SelfDualLoc.hform (PI.SelfDualLoc.sigR σ (Fv F v)) (J.map (PI.SelfDualLoc.inclE (F := F) (Fv F v))) z y) := by
  simp only [hR, Formalism.UG.hform, PI.SelfDualLoc.hform, map_sum, map_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [swVv, sig_swap, incl_swap]

section Rings

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev Sv : Subring (E ⊗[F] Fv F v) :=
  PI.SelfDualLoc.tensInt (F := F) (Fv F v) (PI.SelfDualLoc.intOE E) (v.adicCompletionIntegers F).toSubring

theorem oev_gen (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

theorem oev_mul {s t : Fv F v ⊗[F] E} (hs : s ∈ OEv (E := E) v) (ht : t ∈ OEv (E := E) v) :
    s * t ∈ OEv (E := E) v := by
  first | exact UpperTheory.Reformulated.B.Qh24.oev_mul .. | (apply UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh24.oev_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t hs ht | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t hs | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s t | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v s | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› v | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E ‹_› | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F E | exact @UpperTheory.Reformulated.B.Qh24.oev_mul F

theorem oev_alg (c : v.adicCompletionIntegers F) : ((c : Fv F v) ⊗ₜ[F] (1 : E)) ∈ OEv (E := E) v := by
  have h : ((c : Fv F v) ⊗ₜ[F] (1 : E)) = c • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
    simp [inclR, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c (oev_gen v 1)

theorem swp_mem_oev {s : E ⊗[F] Fv F v} (hs : s ∈ Sv (E := E) v) : swp v s ∈ OEv (E := E) v := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩
    · exact oev_gen v b
    · exact oev_alg v ⟨c, hc⟩
  | zero => rw [map_zero]; exact zero_mem (Submodule.span _ _)
  | one => rw [map_one]; simpa using oev_gen v (E := E) 1
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (S := Submodule _ _) hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem (S := Submodule _ _) hx
  | mul x y _ _ hx hy => rw [map_mul]; exact oev_mul v hx hy

theorem oev_swp {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) : ∃ s ∈ Sv (E := E) v, swp v s = t := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    refine ⟨(a : E) ⊗ₜ[F] (1 : Fv F v), Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩), ?_⟩
    rfl
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨s + s', add_mem hs hs', map_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨((1 : E) ⊗ₜ[F] (c : Fv F v)) * s,
      mul_mem (Subring.subset_closure (Or.inr ⟨c, rfl⟩)) hs, ?_⟩
    rw [map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

end Rings

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E))

theorem oev_smul_lat {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v) {w : Fin n → Fv F v ⊗[F] E}
    (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) : (fun i => t * w i) ∈ latLoc v (Lb : Set (Fin n → E)) := by
  unfold OEv at ht
  rw [SetLike.mem_coe] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine Submodule.subset_span ⟨a • x, Lb.smul_mem a hx, ?_⟩
      funext i
      simp [ratV, map_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
      funext i; simp
    | add y z _ _ hy hz =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (y + z) i) =
          (fun i => inclR (F := F) (Fv F v) (a : E) * y i) + (fun i => inclR (F := F) (Fv F v) (a : E) * z i) := by
        funext i; simp [mul_add]
      rw [e]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : (fun i => inclR (F := F) (Fv F v) (a : E) * (c • y) i) =
          c • (fun i => inclR (F := F) (Fv F v) (a : E) * y i) := by
        funext i; simp [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ c hy
  | zero =>
    convert zero_mem (latLoc v (Lb : Set (Fin n → E))) using 1
    funext i; simp
  | add x y _ _ hx hy =>
    have e : (fun i => (x + y) * w i) = (fun i => x * w i) + (fun i => y * w i) := by funext i; simp [add_mul]
    rw [e]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (fun i => (c • x) * w i) = c • (fun i => x * w i) := by funext i; simp [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ c hx

theorem swVv_mem_latLoc {z : Fin n → E ⊗[F] Fv F v}
    (hz : z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb) :
    swVv v z ∈ latLoc v (Lb : Set (Fin n → E)) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [swVv_incl]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : swVv v (0 : Fin n → E ⊗[F] Fv F v) = 0 := by funext i; simp [swVv]
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : swVv v (x + y) = swVv v x + swVv v y := by funext i; simp [swVv]
    rw [this]; exact add_mem hx hy
  | smul s x _ hx =>
    have : swVv v (s • x) = fun i => swp v (s : E ⊗[F] Fv F v) * swVv v x i := by
      funext i; simp [swVv, Submodule.coe_smul_of_tower, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]
    exact oev_smul_lat v Lb (swp_mem_oev v s.2) hx

theorem latLoc_swVv {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc v (Lb : Set (Fin n → E))) :
    ∃ z ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb, swVv v z = w := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, swVv_incl v x⟩
  | zero => exact ⟨0, zero_mem _, by funext i; simp [swVv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', by funext i; simp [swVv]⟩
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    have hc : ((1 : E) ⊗ₜ[F] (c : Fv F v)) ∈ Sv (E := E) v := Subring.subset_closure (Or.inr ⟨c, rfl⟩)
    refine ⟨(⟨_, hc⟩ : Sv (E := E) v) • z, Submodule.smul_mem _ _ hz, ?_⟩
    funext i
    simp only [swVv, Pi.smul_apply]
    rw [Subring.smul_def, smul_eq_mul, map_mul, swp_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl

theorem isSDLoc_of (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hfg : Lb.FG)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, PI.SelfDualLoc.hform (σ : E →+* E) J x y ∈ PI.SelfDualLoc.intOE E) → y ∈ Lb) :
    IsSDLoc σ J v (Lb : Set (Fin n → E)) := by
  have hT : ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
    rw [Nat.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have key := self_dual_local F E n σ J v Lb 1 (Module.Finite.iff_fg.2 hfg) hint
    (fun y hy => by simpa using hdual y hy) hT
  intro y'
  obtain ⟨y, rfl⟩ := swVv_surjective (E := E) v y'
  have hlat : swVv v y ∈ latLoc v (Lb : Set (Fin n → E)) ↔
      y ∈ PI.SelfDualLoc.latS (F := F) (Fv F v) (Sv (E := E) v) Lb := by
    constructor
    · intro h
      obtain ⟨z, hz, e⟩ := latLoc_swVv v Lb h
      rwa [← swVv_injective v e]
    · exact swVv_mem_latLoc v Lb
  rw [hlat, key]
  constructor
  · intro h x' hx'
    obtain ⟨z, hz, rfl⟩ := latLoc_swVv v Lb hx'
    rw [hR_swap]
    exact swp_mem_oev v (h z hz)
  · intro h z hz
    have h1 := h (swVv v z) (swVv_mem_latLoc v Lb hz)
    rw [hR_swap] at h1
    obtain ⟨s, hs, e⟩ := oev_swp v h1
    rwa [← (swp v).injective e]

end Lat

theorem sdLocX_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : PlX X) :
    IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
  isSDLoc_of v X.B.I.L X.B.I.cm.sig X.B.I.J X.B.I.L_fg
    (fun x hx y hy => (X.B.I.L_dual y).1 hy x hx) (fun y h => (X.B.I.L_dual y).2 h)

end Formalism.L2.SG.Pf.MassDataX.SDL
end
end

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

def SDLocX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), IsSDLoc X.B.I.cm.sig X.B.I.J v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def UnramTypX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : PlX X), TypAt X v → UnramAt (E := X.B.I.E) v

def STypIdx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X), X.MeasTie hb →
    ((X.measW u).μSv p.1).IsHaarMeasure →
    ((X.measW u).μSv p.1 (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1)).toReal =
      ((glkC D.R.k (gOf p) : ℕ) : ℝ) / ((ukC D.R.k (gOf p) : ℕ) : ℝ) *
        ((X.measW u).μSv p.1 (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb u) p.1)).toReal

theorem gAt_mem {D : D7} (X : HidaSetting D) (p : TypX X) : ((gAt X p.1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
  obtain ⟨p, hp⟩ := p
  have hT : IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) p := by
    unfold typSet at hp
    split_ifs at hp with hfin
    · simpa using hp
    · simp at hp
  unfold gAt
  split_ifs with h0
  · exact h0
  · unfold IsTyped at hT
    exact hT.resolve_left h0

section Main

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.MassDataConc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inTypedC_loc (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) (hψ : IsCharAF X.B.I.F ψ) (hψs : IsStdChar ψ) :
    InTypedC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro hX _hP hL hL' hTF p
  have hlat : ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧
      (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    ⟨X.B.I.L, ⟨X.B.I.L_fg, X.B.I.L_span⟩, rfl⟩
  have hTyp : TypAt X p.1 := p.2
  refine ⟨?_, hI X hb u p hX.1 (hL p.1).2.1, hI X hb u' p hX.1 (hL' p.1).2.1⟩
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ p.1 (gAt X p.1) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hψs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (hSD X p.1) (hUn X p.1 hTyp) hlat (hTF p).1 (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL p.1).1 _ (hL p.1).2.1 (hL p.1).2.2.1 _ (hL' p.1).2.1 (hL' p.1).2.2.1 (hL p.1).2.2.2 (hL' p.1).2.2.2
  show MX X u u' ψ p.1 / localVolumeUnit X ψ p.1 = _
  unfold MX localVolumeUnit OmX
  rw [if_pos hTyp, if_pos hTyp]
  exact h

theorem typedAll_of (hSD : SDLocX) (hUn : UnramTypX) (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll := by
  intro D T u u' X0 sd C Th Q i0 i0' νq
  exact inTypedC_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSD hUn hI T.ψ_char T.ψ_std

theorem typedAll_of_idx (hI : STypIdx) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.TypedAll :=
  typedAll_of (fun X v => Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v)
    (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) hI

end Main

end Formalism.L2.SG.Pf.MassDataX
end
end
