import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.RhoPf

open Formalism.L2.SG.TypedSets

section Abstract

variable {G : Type} [Group G]

theorem mem_map_conj (K : Subgroup G) (x a : G) :
    a ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * a * x ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem stab_eq_map (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom =
      (Γ ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj γ).toMonoidHom := by
  ext a
  rw [Subgroup.mem_inf, mem_map_conj, mem_map_conj, Subgroup.mem_inf, mem_map_conj]
  have e1 : (γ * x * k)⁻¹ * a * (γ * x * k) = k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k := by group
  have e2 : x⁻¹ * (γ⁻¹ * a * γ) * x = k * (k⁻¹ * (x⁻¹ * (γ⁻¹ * a * γ) * x) * k) * k⁻¹ := by group
  constructor
  · rintro ⟨ha, hK⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) ha) hγ, ?_⟩
    rw [e1] at hK
    rw [e2]
    exact K.mul_mem (K.mul_mem hk hK) (K.inv_mem hk)
  · rintro ⟨ha, hK⟩
    refine ⟨?_, ?_⟩
    · have e3 : a = γ * (γ⁻¹ * a * γ) * γ⁻¹ := by group
      rw [e3]
      exact Γ.mul_mem (Γ.mul_mem hγ ha) (Γ.inv_mem hγ)
    · rw [e1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hK) hk

theorem card_conj_eq (Γ K : Subgroup G) (x γ k : G) (hγ : γ ∈ Γ) (hk : k ∈ K) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (γ * x * k)).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  rw [stab_eq_map Γ K x γ k hγ hk]
  exact Subgroup.card_map_of_injective (MulAut.conj γ).injective

theorem card_out_eq (Γ K : Subgroup G) (x : G) :
    Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out (DoubleCoset.mk Γ K x))).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨γ, k, hγ, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
  rw [h]
  exact card_conj_eq Γ K x γ k hγ hk

end Abstract

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem massCl_comap (e : G' ≃* G) (Γ K : Subgroup G) :
    massCl (Γ.comap e.toMonoidHom) (K.comap e.toMonoidHom) = massCl Γ K := by
  set Γ' := Γ.comap e.toMonoidHom with hΓ'
  set K' := K.comap e.toMonoidHom with hK'
  have hstab : ∀ y : G', Nat.card ↥(Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom) =
      Nat.card ↥(Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom) := by
    intro y
    have hm : (Γ' ⊓ K'.map (MulAut.conj y).toMonoidHom).map e.toMonoidHom =
        Γ ⊓ K.map (MulAut.conj (e y)).toMonoidHom := by
      ext a
      rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, mem_map_conj, mem_map_conj]
      simp [hΓ', hK', Subgroup.mem_comap, map_mul, map_inv]
    rw [← hm, Subgroup.card_map_of_injective e.injective]
  unfold massCl
  refine finsum_eq_of_bijective (fun c => DoubleCoset.mk Γ K (e (Quotient.out c))) ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (DoubleCoset.eq Γ K _ _).mp h
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    refine (DoubleCoset.eq Γ' K' _ _).mpr
      ⟨e.symm γ, by simpa [hΓ'] using hγ, e.symm k, by simpa [hK'] using hk, ?_⟩
    apply e.injective
    simp [map_mul, h2]
  · intro c
    obtain ⟨γ, k, hγ, hk, hout⟩ := DoubleCoset.mk_out_eq_mul Γ' K' (e.symm (Quotient.out c))
    refine ⟨DoubleCoset.mk Γ' K' (e.symm (Quotient.out c)), ?_⟩
    show DoubleCoset.mk Γ K (e (Quotient.out (DoubleCoset.mk Γ' K' (e.symm (Quotient.out c))))) = c
    rw [hout]
    conv_rhs => rw [← Quotient.out_eq c]
    refine ((DoubleCoset.eq Γ K _ _).mpr ⟨e γ, hγ, e k, hk, ?_⟩).symm
    simp [map_mul]
  · intro c
    rw [card_out_eq, hstab]

end Transport

section Count

variable {G α : Type} [Group G]

theorem massCl_eq_sum (Γ K : Subgroup G) (S : Finset α) (ℓ : G → α) (w : α → ℝ)
    (hS : ∀ x, ℓ x ∈ S)
    (hrel : ∀ x y, ℓ x = ℓ y ↔ ∃ γ ∈ Γ, ∃ k ∈ K, y = γ * x * k)
    (hsurj : ∀ s ∈ S, ∃ x, ℓ x = s)
    (hw : ∀ x, ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℕ) : ℝ)⁻¹ = w (ℓ x)) :
    massCl Γ K = ∑ s ∈ S, w s := by
  unfold massCl
  have hout : ∀ x, ∃ γ ∈ Γ, ∃ k ∈ K, Quotient.out (DoubleCoset.mk Γ K x) = γ * x * k := by
    intro x
    obtain ⟨γ, k, hγ, hk, h⟩ := DoubleCoset.mk_out_eq_mul Γ K x
    exact ⟨γ, hγ, k, hk, h⟩
  rw [← Finset.sum_coe_sort S w, ← finsum_eq_sum_of_fintype]
  refine finsum_eq_of_bijective (fun c => (⟨ℓ (Quotient.out c), hS _⟩ : {s // s ∈ S}))
    ⟨?_, ?_⟩ ?_
  · intro c1 c2 h
    have h' : ℓ (Quotient.out c1) = ℓ (Quotient.out c2) := congrArg Subtype.val h
    obtain ⟨γ, hγ, k, hk, h2⟩ := (hrel _ _).mp h'
    rw [← Quotient.out_eq c1, ← Quotient.out_eq c2]
    exact (DoubleCoset.eq Γ K _ _).mpr ⟨γ, hγ, k, hk, h2⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, rfl⟩ := hsurj s hs
    refine ⟨DoubleCoset.mk Γ K x, Subtype.ext ?_⟩
    obtain ⟨γ, hγ, k, hk, h⟩ := hout x
    exact ((hrel _ _).mpr ⟨γ, hγ, k, hk, h⟩).symm
  · intro c
    exact hw _

end Count

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField IsDedekindDomain

namespace Formalism.L2.SG.RhoPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.PoincareInHH.PoincareSetting

section General

theorem uj_map_iff {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A ≃+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) :
    g ∈ Formalism.UG.UJ σA JA ↔ Units.mapEquiv φ.mapMatrix.toMulEquiv g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  change Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA ↔
    Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have key : Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ =
      (Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, map_mul, hσ]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Matrix.map_injective φ.injective h

end General

section Comm

variable (I : Formalism.MainNotions.S.AutInst)

abbrev cE : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃ₐ[I.F] Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E :=
  Algebra.TensorProduct.comm I.F I.E (Formalism.MainNotions.S.Af I.F)

def psi0 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ≃* GL (Fin I.n) (Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E) :=
  Units.mapEquiv (cE I).toRingEquiv.mapMatrix.toMulEquiv

theorem coe_psi0_eq_map_cE (g : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    ((psi0 I g : GL (Fin I.n) (Formalism.MainNotions.S.Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).map (cE I) := rfl

theorem c_sig (t : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    cE I (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) t) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.S.Af I.F) I.cm.sig (cE I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem c_inclE (x : I.E) : cE I (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af I.F) x := by
  simp [Formalism.UG.inclE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem mem_upts_iff (g : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) ↔ psi0 I g ∈ HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := by
  have h := uj_map_iff (cE I).toRingEquiv (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F))
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.S.Af I.F) I.cm.sig) (fun a => c_sig I a)
    (I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) g
  have hJ : (I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))).map (cE I).toRingEquiv =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.S.Af I.F) I.J := by
    ext i j
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, c_inclE]
  rw [hJ] at h
  exact h

theorem upts_map : (Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F)).map (psi0 I).toMonoidHom =
    HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_upts_iff I g).1 hg
  · intro hx
    refine ⟨(psi0 I).symm x, ?_, ?_⟩
    · exact (mem_upts_iff I _).2 (by rw [MulEquiv.apply_symm_apply]; exact hx)
    · simp

def psiR : I.Gf ≃* ↥(HR (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J) :=
  (MulEquiv.subgroupMap (psi0 I) (Formalism.UG.UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F))).trans
    (MulEquiv.subgroupCongr (upts_map I))

def psi1 : I.Gf ≃* HA (Formalism.MainNotions.S.Af I.F) I.cm.sig I.J := psiR I

theorem adelic_action_matrix (x : I.Gf) : HA.mat _ _ _ (psi1 I x) = psi0 I x := rfl

end Comm

section KBridge

variable (I : Formalism.MainNotions.S.AutInst)

theorem prF_eq (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) : prF I t = cE I (tauF I t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    first
    | rfl
    | simp only [prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, cE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.snd_apply, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem kset_iff (x : I.Gf) : x ∈ I.Kset ↔
    ∀ v : HeightOneSpectrum (𝓞 I.F), compV v (psi0 I x) ∈ Kloc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨e, he⟩ := Formalism.L2.SG.Closed.AdBridgeIso_holds I
  have hfin : I.fmat x = ofHAFin I (e (1, x)) := (he (1, x)).2
  have key := adelic_compact_finite_places I (e (1, x))
  have hm : Formalism.UG.bc (prF I)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J (e (1, x))) = psi0 I x := by
    apply Units.ext
    rw [coe_psi0_eq_map_cE]
    show _ = (I.fmat x).map (cE I)
    rw [hfin]
    simp only [ofHAFin, Matrix.map_map]
    ext i j
    simp [Formalism.UG.bc, prF_eq]
  rw [← hm, ← key, ← hfin]
  exact Iff.rfl

end KBridge

section OnX

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ratV_eq (y : Fin X.B.I.n → X.B.I.E) :
    ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y = fun i => cE X.B.I (incl X.B.I y i) := by
  funext i
  simp [ratV, Formalism.L2.SG.HidaSetting.incl, c_inclE]

theorem linear_adelic_action (x : X.B.I.Gf) (y : Fin X.B.I.n → X.B.I.E) :
    lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x) (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      fun i => cE X.B.I ((X.B.I.fmat x *ᵥ incl X.B.I y) i) := by
  rw [ratV_eq]
  funext i
  simp only [lin, Matrix.mulVecLin_apply, adelic_action_matrix, coe_psi0_eq_map_cE]
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem linear_adelic_action_fixed_iff (x : X.B.I.Gf) (y : Fin X.B.I.n → X.B.I.E) :
    lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x) (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y ↔ X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y := by
  rw [linear_adelic_action, ratV_eq]
  constructor
  · intro h
    funext i
    exact (cE X.B.I).injective (congrFun h i)
  · intro h
    rw [h]

theorem tupH_mem (b : Fin (D.R.rS + 1 + D.R.rS)) : tupH (frameOf X u) b ∈ fixSet X u := by
  induction b using Fin.addCases with
  | left c =>
    induction c using Fin.lastCases with
    | last =>
      simp [tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]
    | cast d =>
      simp [tupH, F0, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]
  | right c =>
    simp [tupH, frameOf, fixSet, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]

theorem mem_tupH (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    ∃ b, tupH (frameOf X u) b = y := by
  simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl
  · exact ⟨Fin.castAdd _ (Fin.castSucc a), by
      simp [tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.eR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩
  · exact ⟨Fin.natAdd _ a, by
      simp [tupH, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.fR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩
  · exact ⟨Fin.castAdd _ (Fin.last _), by
      simp [tupH, F0, frameOf, Formalism.L2.SG.HidaSetting.HidaSetting.zR, Formalism.L2.SG.HidaSetting.HidaSetting.crd]⟩

theorem mem_hsub_iff (x : X.B.I.Gf) :
    x ∈ Hfin X u ↔ psi1 X.B.I x ∈ Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  have hs : psi1 X.B.I x ∈ Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      ∀ b, lin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (psi1 X.B.I x)
          (ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b)) =
        ratV (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (tupH (frameOf X u) b) := by
    first
    | exact mem_stabT _ _ _ _ _
    | exact mem_stabT _ _
    | simp only [Hsub, mem_stabT]
  rw [hs]
  simp only [linear_adelic_action_fixed_iff]
  change (∀ y ∈ fixSet X u, _) ↔ _
  constructor
  · intro hx b
    exact hx _ (tupH_mem X u b)
  · intro hx y hy
    obtain ⟨b, rfl⟩ := mem_tupH X u y hy
    exact hx b

theorem hfin_map : (Hfin X u).map (psi1 X.B.I).toMonoidHom =
    Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_hsub_iff X u x).1 hx
  · intro hy
    refine ⟨(psi1 X.B.I).symm y, ?_, ?_⟩
    · exact (mem_hsub_iff X u _).2 (by rw [MulEquiv.apply_symm_apply]; exact hy)
    · simp

def psiH : Hfin X u ≃* ↥(Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (MulEquiv.subgroupMap (psi1 X.B.I) (Hfin X u)).trans (MulEquiv.subgroupCongr (hfin_map X u))

theorem psiH_val (h : Hfin X u) :
    ((psiH X u h : ↥(Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      HA (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) = psi1 X.B.I h := rfl

def gamR : Subgroup (Hfin X u) :=
  ((HFinIn (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J)).subgroupOf
    (Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).comap (psiH X u).toMonoidHom

def kR : Subgroup (Hfin X u) :=
  ((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
    (Hsub (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).comap (psiH X u).toMonoidHom

theorem massH_eq : massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) =
    massCl (gamR X u) (kR X u) := by
  exact (massCl_comap (psiH X u) _ _).symm

theorem mem_gamR_iff (h : Hfin X u) : h ∈ gamR X u ↔
    ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (h : X.B.I.Gf) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
        (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) := by
  have hsig : ((X.B.I.cm.sig : X.B.I.E →ₐ[X.B.I.F] X.B.I.E) : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E :=
    RingHom.ext fun _ => rfl
  have e1 : h ∈ gamR X u ↔
      psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈
        HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J := by
    first
    | exact Iff.rfl
    | (simp only [gamR, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf, psiH_val,
        HFinIn]; exact Iff.rfl)
  have e2 : psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈
        HFin (Formalism.MainNotions.S.Af X.B.I.F) X.B.I.cm.sig X.B.I.J ↔
      ∃ M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J,
        Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) M =
          psi0 X.B.I ((h : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) := by
    rw [← hsig]
    exact Iff.rfl
  have hmap : ∀ N : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E,
      (N.map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))).map (cE X.B.I) =
        N.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) := by
    intro N
    ext i j
    simp [c_inclE]
  rw [e1, e2]
  refine exists_congr fun M => and_congr_right fun _ => ?_
  have hbc : ((Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) M :
      GL (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.MainNotions.S.Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.S.Af X.B.I.F)) := rfl
  rw [Units.ext_iff, hbc, coe_psi0_eq_map_cE, ← hmap]
  constructor
  · intro hM
    exact (Matrix.map_injective (cE X.B.I).injective hM).symm
  · intro hM
    exact congrArg (fun N => N.map (cE X.B.I)) hM.symm

theorem mem_kR_iff (h : Hfin X u) : h ∈ kR X u ↔ (h : X.B.I.Gf) ∈ X.B.I.Kset := by
  rw [kset_iff]
  first
  | exact Iff.rfl
  | (simp only [kR, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Kf, Subgroup.mem_iInf]; exact Iff.rfl)

end OnX

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Kset

variable (I : Formalism.MainNotions.S.AutInst)

theorem kset_inv' {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem kset_mul' {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem kset_act {k : I.Gf} (hk : k ∈ I.Kset) (w : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    I.fmat k *ᵥ w ∈ I.Lf ↔ w ∈ I.Lf := (hk w).symm

theorem fmat_mul' (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

theorem fmat_inv_mul' (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

end Kset

section Lat

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def lat (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V := Classical.choose (latSub X u h)

theorem lat_coe (h : Hfin X u) : (lat X u h : Set (VS D).V) = latOf X u h :=
  Classical.choose_spec (latSub X u h)

theorem mem_lat (h : Hfin X u) (y : (VS D).V) :
    y ∈ lat X u h ↔ X.B.I.fmat ((h : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [← SetLike.mem_coe, lat_coe]
  show X.B.I.fmat (((h : X.B.I.Gf)) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I (X.xu_K u))]

theorem matE_fix (M : GL (Fin X.B.I.n) X.B.I.E)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) (y : (VS D).V) (hy : X.crd y ∈ fixSet X u) : matE X M y = y := by
  have h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y) := by
    rw [matE_incl]
    exact hfix _ hy
  apply X.bas.equivFun.injective
  funext i
  exact X.ιE.symm.injective (inclInj_holds X (congrFun h1 i))

theorem matE_stab (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) : matE X M ∈ stabF D (X.Fu u) := by
  refine ⟨matE_isom X M hM, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact matE_fix X u M hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · show matE X M (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact matE_fix X u M hfix _ (Or.inr rfl)

theorem hfin_fix (g : Hfin X u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (g : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := g.2 y hy

theorem mem_gmap (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (y : (VS D).V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap γ Λ ↔ γ.symm y ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨γ.symm y, hy, by simp⟩

theorem lat_act (g h k : Hfin X u) (M : GL (Fin X.B.I.n) X.B.I.E)
    (hM : X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)))
    (hk : (k : X.B.I.Gf) ∈ X.B.I.Kset) :
    lat X u (g * h * k) = Formalism.HermitianLatticesTheory.gmap (matE X M) (lat X u h) := by
  ext y
  rw [mem_gmap, mem_lat, mem_lat]
  have hinc : incl X.B.I (X.crd ((matE X M).symm y)) = X.B.I.fmat ((g : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) := by
    have h1 := matE_incl X M ((matE X M).symm y)
    rw [LinearEquiv.apply_symm_apply, ← hM] at h1
    rw [h1, Matrix.mulVec_mulVec, fmat_inv_mul', Matrix.one_mulVec]
  rw [hinc, Matrix.mulVec_mulVec]
  show X.B.I.fmat (((g : X.B.I.Gf) * (h : X.B.I.Gf) * (k : X.B.I.Gf)))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I hk), _root_.mul_inv_rev, fmat_mul']

end Lat

section Cls

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def cls (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V :=
  if hh : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) then Classical.choose hh else ⊥

variable {X u what₂}

theorem cls_spec (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    cls X u what₂ h ∈ what₂ ∧ Eqv X u (cls X u what₂ h) (lat X u h) := by
  have hex : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) :=
    (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).exists
  unfold cls
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem cls_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) {h : Hfin X u}
    {Λ' : Submodule (𝓞 D.host.E) (VS D).V} (h1 : Λ' ∈ what₂) (h2 : Eqv X u Λ' (lat X u h)) :
    cls X u what₂ h = Λ' :=
  (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).unique (cls_spec hR hL h) ⟨h1, h2⟩

theorem gamR_mat {g : Hfin X u} (hg : g ∈ gamR X u) :
    ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  (mem_gamR_iff X u g).1 hg

theorem cls_rel (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (h h' : Hfin X u) :
    cls X u what₂ h = cls X u what₂ h' ↔ ∃ g ∈ gamR X u, ∃ k ∈ kR X u, h' = g * h * k := by
  constructor
  · intro hc
    have e1 := (cls_spec hR hL h).2
    have e2 := (cls_spec hR hL h').2
    rw [hc] at e1
    have e3 : Eqv X u (lat X u h) (lat X u h') := (eqvEquiv X u).trans ((eqvEquiv X u).symm e1) e2
    obtain ⟨g, k, hh', hkl⟩ := hI h h' (lat X u h) (lat X u h') (lat_coe X u h) (lat_coe X u h') e3
    refine ⟨iotaF X u g, ?_, k, ?_, hh'⟩
    · rw [mem_gamR_iff]
      obtain ⟨hGF, -⟩ := Subgroup.mem_inf.1 g.2
      have hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset := hGF
      obtain ⟨M, hM, -, hf⟩ := hGF'
      exact ⟨M, hM, hf⟩
    · rw [mem_kR_iff]
      have hK := Formalism.L2.SG.Pf.LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by rw [← hkl]; exact Iff.rfl)
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u := by group
      rw [e4] at hK
      have e5 : (k : X.B.I.Gf) = X.xu u * ((X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
  · rintro ⟨g, hg, k, hk, rfl⟩
    obtain ⟨M, hM, hMf⟩ := gamR_mat hg
    have hst : matE X M ∈ stabF D (X.Fu u) := matE_stab X u M hM (fun y hy => by
      rw [← hMf]; exact hfin_fix X u g y hy)
    have e1 := (cls_spec hR hL h).2
    have e2 : Eqv X u (lat X u h) (lat X u (g * h * k)) :=
      ⟨matE X M, hst, (lat_act X u g h k M hMf ((mem_kR_iff X u k).1 hk)).symm⟩
    exact (cls_eq hR hL (cls_spec hR hL h).1 ((eqvEquiv X u).trans e1 e2)).symm

theorem cls_surj (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hS : LatSurj X u)
    (s : Submodule (𝓞 D.host.E) (VS D).V) (hs : s ∈ what₂) : ∃ h, cls X u what₂ h = s := by
  obtain ⟨h, Λ', hΛ', he⟩ := hS s (hR.1 s hs)
  have e1 : Λ' = lat X u h := SetLike.coe_injective (hΛ'.trans (lat_coe X u h).symm)
  rw [e1] at he
  exact ⟨h, cls_eq hR hL hs ((eqvEquiv X u).symm he)⟩

end Cls

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {D : D7} (X : HidaSetting D)

def matOf (γ : (VS D).V →ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (LinearMap.toMatrix X.bas X.bas γ).map X.ιE.symm

theorem matOf_comp (γ δ : (VS D).V →ₗ[D.host.E] (VS D).V) : matOf X (γ ∘ₗ δ) = matOf X γ * matOf X δ := by
  unfold matOf
  rw [LinearMap.toMatrix_comp X.bas X.bas X.bas]
  simpa using map_mul X.ιE.symm.mapMatrix (LinearMap.toMatrix X.bas X.bas γ) (LinearMap.toMatrix X.bas X.bas δ)

theorem matOf_id : matOf X LinearMap.id = 1 := by
  unfold matOf
  rw [LinearMap.toMatrix_id]
  simp

theorem crd_apply (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (γ y) = matOf X γ *ᵥ X.crd y := by
  funext i
  show X.ιE.symm (X.bas.repr (γ y) i) = _
  rw [← LinearMap.toMatrix_mulVec_repr X.bas X.bas γ y]
  exact RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) _ _ i

theorem crd_inj : Function.Injective (X.crd) := fun _ _ h =>
  X.bas.repr.injective (Finsupp.ext fun i => X.ιE.symm.injective (congrFun h i))

def glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : GL (Fin X.B.I.n) X.B.I.E where
  val := matOf X γ.toLinearMap
  inv := matOf X γ.symm.toLinearMap
  val_inv := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp
  inv_val := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp

theorem matE_glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matE X (glOf X γ) = γ := by
  apply LinearEquiv.ext
  intro y
  apply crd_inj X
  rw [matE_crd]
  exact (crd_apply X γ.toLinearMap y).symm

theorem matE_inj {M M' : GL (Fin X.B.I.n) X.B.I.E} (h : matE X M = matE X M') : M = M' := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← LatDictK.crd_vOf X x, ← matE_crd, ← matE_crd, h]

theorem hT_coord (x y : (VS D).V) :
    (VS D).hT x y = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by
  rw [hT_expand X x y]
  simp only [← X.J_eq]
  rw [qform]

theorem form_ext {m : Type} [Fintype m] [DecidableEq m] {P Q : Matrix m m D.host.E}
    (h : ∀ a c : m → D.host.E, star a ⬝ᵥ (P *ᵥ c) = star a ⬝ᵥ (Q *ᵥ c)) : P = Q := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : D.host.E) : m → D.host.E) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  rw [hs] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mapM_cT (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) M) = (mapM X M)ᴴ := by
  ext i j
  simp only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT,
    Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]

theorem glOf_unitary (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    glOf X γ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  set A := mapM X ((glOf X γ : GL _ _) : Matrix _ _ _) with hA
  have hrep : ∀ y, X.bas.equivFun (γ y) = A *ᵥ X.bas.equivFun y := by
    intro y
    rw [hA, ← matE_repr, matE_glOf]
  have key : Aᴴ * mapM X X.B.I.J * A = mapM X X.B.I.J := by
    apply form_ext
    intro a c
    have h1 := hγ (X.bas.equivFun.symm a) (X.bas.equivFun.symm c)
    rw [hT_coord, hT_coord, hrep, hrep, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [← h1, Matrix.star_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show Formalism.UG.cT (starRingEnd X.B.I.E) ((glOf X γ : GL _ _) : Matrix _ _ _) * X.B.I.J * ((glOf X γ : GL _ _) : Matrix _ _ _) =
    X.B.I.J
  apply Matrix.map_injective X.ιE.injective
  show mapM X _ = mapM X _
  rw [map_mul, map_mul, mapM_cT]
  exact key

end Mat

section UJ

theorem uj_bc {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A →+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) (hg : g ∈ Formalism.UG.UJ σA JA) : Formalism.UG.bc φ g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  have hg' : Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA := hg
  show Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have hc : Formalism.UG.cT σB ((g : Matrix m m A).map φ) = (Formalism.UG.cT σA (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end UJ

section AH

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def AH (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, γ (X.eX a) = X.eX a) ∧ (∀ a, γ (X.fY a) = X.fY a) ∧
    γ (X.zu u) = X.zu u ∧ Formalism.HermitianLatticesTheory.gmap γ Λ = Λ}

theorem crd_fix_of (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, γ (X.eX a) = X.eX a)
    (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    (glOf X γ : Matrix _ _ _) *ᵥ y = y := by
  have hc : ∀ v, γ v = v → (glOf X γ : Matrix _ _ _) *ᵥ X.crd v = X.crd v := fun v hv => by
    rw [← matE_crd, matE_glOf, hv]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
  · exact hc _ (he a)
  · exact hc _ (hf a)
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hc _ hz

def gOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (he : ∀ a, γ (X.eX a) = X.eX a) (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) : Hfin X u :=
  ⟨⟨Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ),
    uj_bc _ _ _ (fun a => by simp [Formalism.UG.sigR, Formalism.UG.inclE]; rfl) X.B.I.J _ (glOf_unitary X γ hγ)⟩,
    fun y hy => by
      show ((glOf X γ : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))) *ᵥ incl X.B.I y =
        incl X.B.I y
      funext i
      have := (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ : Matrix _ _ _) y i).symm
      rw [crd_fix_of X u γ he hf hz y hy] at this
      exact this⟩


end AH

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Stab

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev stabR (h : Hfin X u) : Subgroup (Hfin X u) := gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom

theorem kset_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem stab_kset {h g : Hfin X u} (hg : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom) :
    ((h⁻¹ * g⁻¹ * h : Hfin X u) : X.B.I.Gf) ∈ X.B.I.Kset := by
  rw [mem_map_conj, mem_kR_iff] at hg
  have e : h⁻¹ * g⁻¹ * h = (h⁻¹ * g * h)⁻¹ := by group
  rw [e, Subgroup.coe_inv]
  exact kset_inv' X.B.I hg

variable {X u}

def matR {g : Hfin X u} (hg : g ∈ gamR X u) : GL (Fin X.B.I.n) X.B.I.E := Classical.choose (gamR_mat hg)

theorem matR_spec {g : Hfin X u} (hg : g ∈ gamR X u) :
    matR hg ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (matR hg : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  Classical.choose_spec (gamR_mat hg)

theorem matR_mem (h g : Hfin X u) (hg : g ∈ stabR X u h) :
    matE X (matR (Subgroup.mem_inf.1 hg).1) ∈ AH X u (lat X u h) := by
  obtain ⟨hM, hMf⟩ := matR_spec (Subgroup.mem_inf.1 hg).1
  have hfix : ∀ y ∈ fixSet X u, (matR (Subgroup.mem_inf.1 hg).1 : Matrix _ _ _).map
      (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ incl X.B.I y = incl X.B.I y := fun y hy => by
    rw [← hMf]; exact hfin_fix X u g y hy
  refine ⟨matE_isom X _ hM, fun a => matE_fix X u _ hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)),
    fun a => matE_fix X u _ hfix _ (Or.inl (Or.inr ⟨a, rfl⟩)), matE_fix X u _ hfix _ (Or.inr rfl), ?_⟩
  have e : g * h * (h⁻¹ * g⁻¹ * h) = h := by group
  have := lat_act X u g h (h⁻¹ * g⁻¹ * h) _ hMf (stab_kset X u (Subgroup.mem_inf.1 hg).2)
  rw [e] at this
  exact this.symm

theorem card_stab (h : Hfin X u) : Nat.card ↥(stabR X u h) = Nat.card ↥(AH X u (lat X u h)) := by
  let Φ : ↥(stabR X u h) → ↥(AH X u (lat X u h)) := fun g =>
    ⟨matE X (matR (Subgroup.mem_inf.1 g.2).1), matR_mem h g g.2⟩
  have hinj : Function.Injective Φ := by
    intro g g' hgg
    have e1 : matE X (matR (Subgroup.mem_inf.1 g.2).1) = matE X (matR (Subgroup.mem_inf.1 g'.2).1) :=
      congrArg Subtype.val hgg
    have e2 := matE_inj X e1
    have f1 := (matR_spec (Subgroup.mem_inf.1 g.2).1).2
    have f2 := (matR_spec (Subgroup.mem_inf.1 g'.2).1).2
    have e3 : X.B.I.fmat ((g : Hfin X u) : X.B.I.Gf) = X.B.I.fmat ((g' : Hfin X u) : X.B.I.Gf) := by
      rw [f1, f2, e2]
    exact Subtype.ext (Subtype.ext (Subtype.ext (Units.ext e3)))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨γ, hγ⟩
    obtain ⟨hi, he, hf, hz, hl⟩ := hγ
    set g := gOf X u γ hi he hf hz with hgdef
    have hgR : g ∈ gamR X u := (mem_gamR_iff X u g).2 ⟨glOf X γ, glOf_unitary X γ hi, rfl⟩
    have hlat : lat X u (g * h * 1) = lat X u h := by
      rw [lat_act X u g h 1 (glOf X γ) rfl (kset_one X), matE_glOf, hl]
    have hgK : g ∈ (kR X u).map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj, mem_kR_iff]
      have hK := LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by
          show y ∈ latOf X u h ↔ y ∈ latOf X u (g * h * 1)
          rw [← lat_coe X u h, ← lat_coe X u (g * h * 1), hlat])
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (((g * h * 1 : Hfin X u) : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        group
      rw [e4] at hK
      have e5 : ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) =
          X.xu u * ((X.xu u)⁻¹ * ((h⁻¹ * g * h : Hfin X u) : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
    have hg : g ∈ stabR X u h := Subgroup.mem_inf.2 ⟨hgR, hgK⟩
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show matE X (matR (Subgroup.mem_inf.1 hg).1) = γ
    have f1 := (matR_spec (Subgroup.mem_inf.1 hg).1).2
    have e6 : matR (Subgroup.mem_inf.1 hg).1 = glOf X γ := by
      apply Units.ext
      apply Matrix.map_injective (inclInj_holds X)
      show ((matR (Subgroup.mem_inf.1 hg).1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) =
        ((glOf X γ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
          (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))
      rw [← f1]
      rfl
    rw [e6, matE_glOf]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Stab

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem inv_apply' (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) : (δ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) y = δ.symm y :=
  rfl

theorem xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp [Fin.is_lt]

theorem st_mul {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (hδ : δ ∈ stabF D F0) :
    γ * δ ∈ stabF D F0 := by
  refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
  · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
  · show γ (δ F0.z) = F0.z
    rw [hδ.2.2, hγ.2.2]

theorem st_inv {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ⁻¹ ∈ stabF D F0 := by
  refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← hγ.2.1 j]
    rw [← kmap_mul, inv_mul_cancel, kmap_one]
  · show γ.symm F0.z = F0.z
    conv_lhs => rw [← hγ.2.2]
    exact γ.symm_apply_apply _

theorem stab_X_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact Submodule.mem_map_of_mem hx

theorem stab_perp_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 := hy _ (stab_X_mem F0 (st_inv F0 hγ) hx)
  have h2 := hγ.1 (γ⁻¹ x) y
  rw [inv_apply', LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact h1

def ind {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun y hy => stab_perp_mem F0 hγ hy))
    (fun x hx => stab_X_mem F0 hγ hx)

theorem ind_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ind F0 hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, stab_perp_mem F0 hγ x.2⟩ := rfl

theorem autLz_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) :
    φ ∈ autLz D F0 Λ ↔ ∃ γ, ∃ hγ : γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ φ = ind F0 hγ := by
  constructor
  · rintro ⟨γ, hγ, hΛ, hφ⟩
    refine ⟨γ, hγ, hΛ, funext fun q => ?_⟩
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    exact (hφ x (stab_perp_mem F0 hγ x.2)).trans rfl
  · rintro ⟨γ, hγ, hΛ, rfl⟩
    exact ⟨γ, hγ, hΛ, fun x hx => rfl⟩

theorem ind_inv_cancel {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 (st_inv F0 hδ) (ind F0 hδ q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ⁻¹ (δ x.1) = x.1
  rw [inv_apply', LinearEquiv.symm_apply_apply]


theorem card_autLz_gmap {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card ↥(autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ)) = Nat.card ↥(autLz D F0 Λ) := by
  let c : (WbQ D F0 → WbQ D F0) → (WbQ D F0 → WbQ D F0) := fun φ => ind F0 hδ ∘ φ ∘ ind F0 (st_inv F0 hδ)
  have hc : Function.Injective c := by
    intro φ ψ hφψ
    funext q
    have h1 := congrFun hφψ (ind F0 hδ q)
    simp only [c, Function.comp, ind_inv_cancel] at h1
    have h2 := congrArg (ind F0 (st_inv F0 hδ)) h1
    rwa [ind_inv_cancel, ind_inv_cancel] at h2
  have hset : autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ) = c '' autLz D F0 Λ := by
    ext ψ
    rw [autLz_iff, Set.mem_image]
    constructor
    · rintro ⟨γ', hγ', hΛ', rfl⟩
      refine ⟨ind F0 (st_mul F0 (st_mul F0 (st_inv F0 hδ) hγ') hδ),
        (autLz_iff F0 Λ _).2 ⟨_, _, ?_, rfl⟩, ?_⟩
      · rw [gmap_mul', gmap_mul', hΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => ?_)
        simp only [c, Function.comp]
        rw [ind_mk, ind_mk, ind_mk, ind_mk]
        congr 1
        apply Subtype.ext
        show δ ((δ⁻¹ * γ' * δ) (δ⁻¹ x.1)) = γ' x.1
        show δ (δ⁻¹ (γ' (δ (δ⁻¹ x.1)))) = γ' x.1
        rw [inv_apply', inv_apply', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨γ, hγ, hΛ, rfl⟩ := (autLz_iff F0 Λ φ).1 hφ
      refine ⟨δ * γ * δ⁻¹, st_mul F0 (st_mul F0 hδ hγ) (st_inv F0 hδ), ?_, ?_⟩
      · rw [gmap_mul', ← gmap_mul' δ⁻¹ δ, inv_mul_cancel, gmap_one', gmap_mul', hΛ]
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => rfl)
  rw [hset]
  exact Nat.card_image_of_injective hc _

end Ind

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section W3

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fuX : (X.Fu u).X = Xs X := by
  rw [FlagG.X, X.Fu_e]
  rfl

theorem AH_stab {Λ : Submodule (𝓞 D.host.E) (VS D).V} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hγ : γ ∈ AH X u Λ) : γ ∈ stabF D (X.Fu u) := by
  obtain ⟨hi, he, -, hz, -⟩ := hγ
  refine ⟨hi, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact he a
  · show γ (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hz

def indA (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : ↥(AH X u Λ)) : WbQ D (X.Fu u) → WbQ D (X.Fu u) :=
  ind (X.Fu u) (AH_stab X u γ.2)

theorem prV_perp (v : (VS D).V) : prV X v ∈ perpS (VS D) (X.Fu u).X := by
  intro x hx
  rw [fuX] at hx
  exact hT_Xs_prV X hx v

theorem prV_fix (w : (VS D).V) (he : ∀ a, (VS D).hT (X.eX a) w = 0) (hf : ∀ a, (VS D).hT (X.fY a) w = 0) :
    prV X w = w := by
  rw [prV_apply]
  simp [he, hf]

theorem prV_of_fix (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hgi : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    prV X (g (prV X v)) = g (prV X v) := by
  have h1 : ∀ a, (VS D).hT (X.eX a) (g (prV X v)) = 0 := fun a => by
    rw [← hge a, hgi, hT_e_prV]
  have h2 : ∀ a, (VS D).hT (X.fY a) (g (prV X v)) = 0 := fun a => by
    rw [← hgf a, hgi, hT_f_prV]
  exact prV_fix X _ h1 h2

theorem fix_sub_prV (g : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hge : ∀ a, g (X.eX a) = X.eX a) (hgf : ∀ a, g (X.fY a) = X.fY a) (v : (VS D).V) :
    g (v - prV X v) = v - prV X v := by
  rw [sub_prV_eq]
  simp [map_sum, map_smul, hge, hgf]

theorem indA_inj (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Function.Injective (indA X u Λ) := by
  intro γ γ' hγγ
  obtain ⟨hi, he, hf, -, -⟩ := γ.2
  obtain ⟨hi', he', hf', -, -⟩ := γ'.2
  apply Subtype.ext
  apply LinearEquiv.ext
  intro y
  have hq := congrFun hγγ (Submodule.Quotient.mk ⟨prV X y, prV_perp X u y⟩)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at hq
  rw [Submodule.Quotient.eq] at hq
  have hd : γ.1 (prV X y) - γ'.1 (prV X y) ∈ Xs X := by
    rw [← fuX X u]
    exact hq
  have h0 := prV_Xs X hd
  rw [map_sub, prV_of_fix X γ.1 hi he hf, prV_of_fix X γ'.1 hi' he' hf', sub_eq_zero] at h0
  calc γ.1 y = γ.1 (y - prV X y) + γ.1 (prV X y) := by rw [← map_add, sub_add_cancel]
    _ = γ'.1 (y - prV X y) + γ'.1 (prV X y) := by
        rw [fix_sub_prV X γ.1 he hf, fix_sub_prV X γ'.1 he' hf', h0]
    _ = γ'.1 y := by rw [← map_add, sub_add_cancel]

theorem mem_lat_gmap (h : Hfin X u) {γ0 : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hΛ : Formalism.HermitianLatticesTheory.gmap γ0 (lat X u h) = lat X u h) :
    (∀ y ∈ latOf X u h, γ0 y ∈ latOf X u h) ∧ (∀ y ∈ latOf X u h, γ0.symm y ∈ latOf X u h) := by
  constructor
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap, LinearEquiv.symm_apply_apply]
    exact hy
  · intro y hy
    rw [← lat_coe] at hy ⊢
    rw [SetLike.mem_coe, ← hΛ, mem_gmap] at hy
    exact hy

theorem autLz_range (h : Hfin X u) : autLz D (X.Fu u) (lat X u h) = Set.range (indA X u (lat X u h)) := by
  ext φ
  rw [autLz_iff]
  constructor
  · rintro ⟨γ0, hγ0, hΛ, rfl⟩
    have hinv : γ0⁻¹ ∈ stabF D (X.Fu u) := st_inv (X.Fu u) hγ0
    let γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := LinearEquiv.ofLinear (gW X γ0) (gW X γ0⁻¹)
      (LinearMap.ext fun y => gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y)
      (LinearMap.ext fun y => gW_gW X u hinv hγ0 (fun w => LinearEquiv.symm_apply_apply γ0 w) y)
    have hm := mem_lat_gmap X u h hΛ
    have hAH : γ ∈ AH X u (lat X u h) := by
      refine ⟨fun x y => gW_isom X u hγ0 x y, fun a => gW_e X a, fun a => gW_f X a, stabilizer_fix_anisotropic X u hγ0, ?_⟩
      ext y
      rw [mem_gmap]
      constructor
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        have := gW_mem X u h h hm.1 hy
        have e : gW X γ0 (γ.symm y) = y := gW_gW X u hγ0 hinv (fun w => LinearEquiv.apply_symm_apply γ0 w) y
        rwa [e] at this
      · intro hy
        rw [← SetLike.mem_coe, lat_coe] at hy ⊢
        exact gW_mem X u h h (fun w hw => hm.2 w hw) hy
    refine ⟨⟨γ, hAH⟩, ?_⟩
    funext q
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    show ind (X.Fu u) (AH_stab X u hAH) (Submodule.Quotient.mk x) = ind (X.Fu u) hγ0 (Submodule.Quotient.mk x)
    rw [ind_mk, ind_mk, Submodule.Quotient.eq]
    show gW X γ0 x.1 - γ0 x.1 ∈ (X.Fu u).X
    apply (show Xs X ≤ (X.Fu u).X from (fuX X u).ge)
    have hx : ∀ a, (VS D).hT (X.eX a) x.1 = 0 := fun a => x.2 _ (by rw [fuX X u]; exact eX_mem_Xs X a)
    have h1 := sub_prV_mem_Xs X hx
    have h2 := stab_Xs X u hγ0 h1
    have h3 := stab_perp X u hγ0 x.1
    have e : gW X γ0 x.1 - γ0 x.1 =
        (x.1 - prV X x.1) - γ0 (x.1 - prV X x.1) - (γ0 (prV X x.1) - prV X (γ0 (prV X x.1))) := by
      rw [gW_apply, map_sub]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3
  · rintro ⟨γ, rfl⟩
    exact ⟨γ.1, AH_stab X u γ.2, γ.2.2.2.2.2, rfl⟩

theorem card_AH (h : Hfin X u) :
    Nat.card ↥(AH X u (lat X u h)) = Nat.card ↥(autLz D (X.Fu u) (lat X u h)) := by
  rw [autLz_range]
  exact (Nat.card_range_of_injective (indA_inj X u _)).symm

end W3

end Formalism.L2.SG.RhoPf
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Final

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem weight_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    ((Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) : ℕ) : ℝ)⁻¹ =
      wRow D (X.Fu u) (cls X u what₂ h) := by
  obtain ⟨-, δ, hδ, hδe⟩ := cls_spec hR hL h
  have e1 : Nat.card ↥(gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom) =
      Nat.card ↥(autLz D (X.Fu u) (cls X u what₂ h)) := by
    rw [show gamR X u ⊓ (kR X u).map (MulAut.conj h).toMonoidHom = stabR X u h from rfl, card_stab, card_AH,
      ← hδe, card_autLz_gmap (X.Fu u) hδ]
  rw [e1]
  rfl

theorem massH_rows (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (hS : LatSurj X u) :
    Formalism.L2.SG.TypedSets.massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (Formalism.L2.SG.TypedSets.frameOf X u) =
      Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) what₂ := by
  rw [massH_eq]
  exact massCl_eq_sum (gamR X u) (kR X u) what₂ (cls X u what₂) (wRow D (X.Fu u))
    (fun h => (cls_spec hR hL h).1) (cls_rel hR hL hI) (cls_surj hR hL hS) (weight_eq X u what₂ hR hL)

end Final

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LatRowLat X u) (hI : Formalism.L2.SG.Pf.LatInj X u) (hS : Formalism.L2.SG.Pf.LatSurj X u) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  Formalism.L2.SG.RhoPf.massH_rows X u (Y.what₂ u) (Y.rowsOK u) hL hI hS

end Formalism.L2.SG.MassDataConc
end
end

section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
end
end
