import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountPOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  obtain ⟨ZX, hbX, heX, hgX, hdX⟩ := hGe X hX hXY
  obtain ⟨ZY, hbY, heY, hgY, hdY⟩ := hGe Y hG.2.2.2.2.2 rfl
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVdEx_holds : OmVdEx X ψ := fun v hS =>
  ⟨(PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).1,
    (PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).2.1⟩

theorem omVdUniq_holds : OmVdUniq X ψ := fun v => omUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem omVdSdW_holds : OmVdSdW X ψ := fun v =>
  SdB.sdVolW_of_perf X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVdSdH_holds : OmVdSdH X ψ := fun v =>
  SdB.sdVolH_of_perf X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVBadT_of_steps (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hM : ∀ v : PlX X, MeasP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hI : ∀ v : PlX X, IdxP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of X u' ψ hStd hLat hGram (omVdEx_holds X ψ) (omVdUniq_holds X ψ)
    (fun v hv => orbP_of _ _ _ _ _ _ _ (hExt v hv))
    (fun v => fibP_of_dual _ _ _ _ _ _ _ (hPC v) (hPD v))
    (fun v hv => countP_of _ _ _ _ _ _ _ (hM v) (hI v) (hCl v hv) (hPC v))
    (omVdSdW_holds X ψ) (omVdSdH_holds X ψ)


end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LatBasOP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

def IdxVP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

theorem localLattice_hasBasis (a : ℕ) (Y : TupV (E := E) v n a) : LatBasOP σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem idxVP_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasOP σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxVP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem idxP_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxVP σ J ψ v Λ a Y) : IdxP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem MeasP₂ (a : ℕ) (Y : TupV (E := E) v n a) : MeasP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := (lamOC_holds v Λ a hG.2.1).1
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem idxP_holds (a : ℕ) (Y : TupV (E := E) v n a) : IdxP σ J ψ v Λ a Y :=
  idxP_of σ J ψ v Λ a Y (idxVP_of σ J ψ v Λ a Y (localLattice_hasBasis σ J ψ v Λ a Y) (resIdx_holds v))

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_primDual_cls (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_steps X u' ψ hStd hLat hGram hExt hPC hPD (fun v => MeasP₂ _ _ _ _ _ _ _)
    (fun v => idxP_holds _ _ _ _ _ _ _) hCl


end Loc

end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem near_int {a : ℕ} (ϖ : Fv F v) (hϖ : IsUnif v ϖ) (A : Fin a → Fin a → Fv F v ⊗[F] E)
    (hA : ∀ i j, A i j ∈ OEv (E := E) v) (d : Fin a → Fv F v ⊗[F] E)
    (hu : ∀ i, d i + sc (E := E) v ϖ * ∑ j, A i j * d j ∈ OEv (E := E) v) : ∀ i, d i ∈ OEv (E := E) v := by
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  have hev : ∀ i, ∀ᶠ k in atTop, ϖ ^ k • d i ∈ OEv (E := E) v := by
    intro i
    have ht : Tendsto (fun k : ℕ => ϖ ^ k • d i) atTop (𝓝 0) := by
      have := hπ.smul_const (d i)
      simpa using this
    exact ht ((isOpen_oEv (E := E) v).mem_nhds (oEv_zero v))
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 hev).exists
  have key : ∀ m : ℕ, (∀ i, sc (E := E) v (ϖ ^ m) * d i ∈ OEv (E := E) v) → ∀ i, d i ∈ OEv (E := E) v := by
    intro m
    induction m with
    | zero =>
      intro h i
      simpa [sc_one] using h i
    | succ m ih =>
      intro h
      apply ih
      intro i
      have hS : ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) =
          sc (E := E) v (ϖ ^ m) * sc (E := E) v ϖ * ∑ j, A i j * d j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, ← sc_mul]
        ring
      have e : sc (E := E) v (ϖ ^ m) * d i = sc (E := E) v (ϖ ^ m) * (d i + sc (E := E) v ϖ * ∑ j, A i j * d j) -
          ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) := by
        rw [hS]
        ring
      rw [e, sub_eq_add_neg]
      exact oEv_add v (sc_mul_mem_oEv v (pow_mem hint m) (hu i))
        (oEv_neg v (oEv_sum v _ _ fun j _ => oEv_mul v (hA i j) (h j)))
  exact key N fun i => by rw [← smul_eq_sc]; exact hN i

theorem primCos_of (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : PrimCos σ J ψ v Λ a := by
  intro hS hL hSD hUn ϖ hϖ X hX Z hZ
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨P, hP, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hZ
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL X hX
  have hPs : ϖ ^ (0 + 1) • P ∈ lamS v Λ a := lamS_smul v Λ (pow_mem hint _) hP
  refine ⟨fun i => (latLoc (E := E) v Λ).add_mem (hX.1 i) (hPs i), fun c hc => ?_⟩
  have hsm : ∀ j i, hR (Fv F v) σ J (W j) ((ϖ ^ (0 + 1) • P) i) = sc (E := E) v ϖ * hR (Fv F v) σ J (W j) (P i) := by
    intro j i
    have := hR_smul_smul σ J v 1 (ϖ ^ (0 + 1)) (W j) (P i)
    rw [one_smul, one_mul, zero_add, pow_one] at this
    rw [zero_add, pow_one]
    exact this
  have hpair : ∀ j, hR (Fv F v) σ J (W j) (∑ i, c i • (X + ϖ ^ (0 + 1) • P) i) =
      c j + sc (E := E) v ϖ * ∑ i, hR (Fv F v) σ J (W j) (P i) * c i := by
    intro j
    rw [hR_sum_smul_right]
    have h1 : ∀ i, c i * hR (Fv F v) σ J (W j) ((X + ϖ ^ (0 + 1) • P) i) =
        c i * (if i = j then 1 else 0) + sc (E := E) v ϖ * (hR (Fv F v) σ J (W j) (P i) * c i) := by
      intro i
      rw [Pi.add_apply, hR_add_right, (hd i j).2, hsm j i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_ite]
  exact near_int v ϖ hϖ (fun j i => hR (Fv F v) σ J (W j) (P i))
    (fun j i => hR_mem_oEv σ J v Λ hSD (hW j) (hP i)) c
    (fun j => by rw [← hpair j]; exact hR_mem_oEv σ J v Λ hSD (hW j) hc)

end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LeftInvO (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), (∀ i k, N i k ∈ OEv (E := E) v) ∧ N * M = 1

theorem primDual_of (a : ℕ) (hB : Red.OBas1 σ J ψ v Λ) (hLI : LeftInvO σ J ψ v (n := n) a) :
    PrimDual σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  obtain ⟨e, he, hg⟩ := hB hS hL hSD hUn
  have hee : ∀ k l, hR (Fv F v) σ J (e k) (e l) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hg k) l
    simpa [gramR, Matrix.one_apply] using this
  have hcoord : ∀ i, ∃ c : Fin n → Fv F v ⊗[F] E, (∀ k, c k ∈ OEv (E := E) v) ∧ y i = ∑ k, c k • e k :=
    fun i => (he (y i)).1 (hy.1 i)
  choose M hM hyM using hcoord
  obtain ⟨N, hN, hNM⟩ := hLI hS hUn (Matrix.of fun k i => M i k) (fun k i => hM i k) (by
    intro c hc i
    apply hy.2 c _ i
    have e1 : ∑ i, c i • y i = ∑ k, Matrix.mulVec (Matrix.of fun k i => M i k) c k • e k := by
      simp only [hyM, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    rw [e1]
    exact (he _).2 ⟨_, hc, rfl⟩)
  have hNM' : ∀ j i, ∑ l, N j l * M i l = if j = i then 1 else 0 := by
    intro j i
    have := congrFun (congrFun hNM j) i
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun j => ∑ l, sigR (Fv F v) σ (N j l) • e l,
    fun j => (he _).2 ⟨_, fun l => UnN.sigR_mem σ v (hN j l), rfl⟩, fun i j => ⟨?_, ?_⟩⟩
  · have h1 : ∀ l, hR (Fv F v) σ J (y i) (e l) = sigR (Fv F v) σ (M i l) := by
      intro l
      rw [hyM i, hR_sum_smul_left]
      simp [hee]
    rw [hR_sum_smul_right]
    simp only [h1]
    have e2 : ∑ l, sigR (Fv F v) σ (N j l) * sigR (Fv F v) σ (M i l) =
        sigR (Fv F v) σ (∑ l, N j l * M i l) := by
      rw [map_sum]
      simp only [map_mul]
    rw [e2, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · have h2 : ∀ k, hR (Fv F v) σ J (∑ l, sigR (Fv F v) σ (N j l) • e l) (e k) = N j k := by
      intro k
      rw [hR_sum_smul_left]
      simp only [hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact PI.VolStabSW.sigR_invol (Fv F v) σ hσ (N j k)
    rw [hyM i, hR_sum_smul_right]
    simp only [h2]
    have e3 : ∑ k, M i k * N j k = ∑ k, N j k * M i k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [e3, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

theorem oBas1_holds : Red.OBas1 σ J ψ v Λ := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  exact Red.oBas1_of_unitV σ J ψ v Λ
    (Orb.unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR))

theorem primDual_of_left (a : ℕ) (hLI : LeftInvO σ J ψ v (n := n) a) : PrimDual σ J ψ v Λ a :=
  primDual_of σ J ψ v Λ a (oBas1_holds σ J ψ v Λ) hLI

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_std_lat_gram (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt
    (fun v => primCos_of _ _ _ _ _ _ (primDual_of_left _ _ _ _ _ _ (hLI v)))
    (fun v => primDual_of_left _ _ _ _ _ _ (hLI v)) hCl

end Loc

end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_red (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_std_lat_gram X u' ψ hStd hLat hGram hExt hLI (fun v hv => clsP_of _ _ _ _ _ _ _ (hRed v hv) hFI hFS)


end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def augT {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) : TupV (E := E) v n (a + 1) :=
  Fin.snoc (α := fun _ => Fin n → Fv F v ⊗[F] E) X w

theorem augT_castSucc {a : ℕ} (X : TupV (E := E) v n a) (w : Fin n → Fv F v ⊗[F] E) (i : Fin a) :
    augT v X w i.castSucc = X i := by
  simp [augT]

def IsoExt (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w : Fin n → Fv F v ⊗[F] E, IsPrim v Λ (augT v X w) ∧ gramR (Fv F v) σ J (augT v X w) = T

theorem extP_of (a : ℕ) (Y : TupV (E := E) v n a) (hn : a + 1 ≤ n) (hI : IsoExt σ J ψ v Λ a Y) :
    ExtP σ J ψ v Λ a Y := by
  intro h hG
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hU : UnitV σ J ψ v Λ :=
    unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR)
  obtain ⟨T, hTu, hext⟩ := hI hG
  obtain ⟨hS, hL, hSD, hUn, -, hP⟩ := hG
  obtain ⟨wY, hPY, hgY⟩ := hext Y hP rfl
  have hGY : GoodY σ J ψ v Λ (a + 1) (augT v Y wY) := ⟨hS, hL, hSD, hUn, hn, hPY, by rw [hgY]; exact hTu⟩
  have hE := extOrth_of σ J ψ v Λ (a + 1) (augT v Y wY) (oSub (E := E) v) (oSmul v Λ)
    (orthoB_of σ J ψ v Λ (a + 1) (augT v Y wY) hU)
  have hT : IsUnit (gramR (Fv F v) σ J (augT v Y wY)).det := by
    obtain ⟨u, -, -, hu⟩ := hTu
    rw [hgY]
    exact ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  refine ⟨gT v hn (gramR (Fv F v) σ J (augT v Y wY)), fun X hX hXY => ?_⟩
  obtain ⟨wX, hPX, hgX⟩ := hext X hX hXY
  obtain ⟨Z, hZb, hZe, hZg⟩ := hE hn hGY (augT v X wX) hPX.1 (by rw [hgX, hgY])
  refine ⟨Z, hZb, fun i => ?_, hZg, isUnit_det_colM σ J v hn _ hT Z hZg⟩
  have e1 : eSp h (Sum.inl i) = eSp hn (Sum.inl i.castSucc) := by
    apply Fin.ext
    simp [eSp]
  rw [e1, hZe i.castSucc, augT_castSucc]

end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem a_succ_le_n : D.R.rS + 1 + D.R.rS + 1 ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := D.R.rS_two
  have h3 := D.R.m_add_three_le_k
  unfold Ranks.r at h1
  omega

theorem omVBadT_of_iso (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoExt X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_red X u' ψ hStd hLat hGram
    (fun v hv => extP_of _ _ _ _ _ _ _ (a_succ_le_n X) (hIso v hv)) hLI hRed hFI hFS


end PI.OmVd
end
end

section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem one_mem_O : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := (PI.OmLocU.Orb.oSub (E := E) v).1

theorem prod_int {m : ℕ} (f : Fin m → Fv F v ⊗[F] E) (hf : ∀ i, f i ∈ OEv (E := E) v) :
    ∏ i, f i ∈ OEv (E := E) v :=
  Finset.prod_induction _ (· ∈ OEv (E := E) v) (fun _ _ => oEv_mul v) (one_mem_O v) (fun i _ => hf i)

theorem det_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    A.det ∈ OEv (E := E) v := by
  rw [Matrix.det_apply]
  refine oEv_sum v _ _ fun p _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> rw [h]
  · rw [one_smul]; exact prod_int v _ fun i => hA _ _
  · rw [Units.neg_smul, one_smul]; exact oEv_neg v (prod_int v _ fun i => hA _ _)

theorem adj_int {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v) :
    ∀ i j, A.adjugate i j ∈ OEv (E := E) v := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_int v _ fun k l => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact one_mem_O v
    · exact oEv_zero v
  · exact hA k l

theorem uniPrim {a : ℕ} (hSD : IsSDLoc σ J v Λ) (X : TupV (E := E) v n a)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ)
    (hu : ∃ u ∈ OEv (E := E) v, (gramR (Fv F v) σ J X).det ∈ OEv (E := E) v ∧ (gramR (Fv F v) σ J X).det * u = 1) :
    IsPrim v Λ X := by
  refine ⟨hX, fun c hc i => ?_⟩
  have hGi : ∀ i j, gramR (Fv F v) σ J X i j ∈ OEv (E := E) v := fun i j => hR_mem_oEv σ J v Λ hSD (hX i) (hX j)
  have hGc : ∀ j, Matrix.mulVec (gramR (Fv F v) σ J X) c j ∈ OEv (E := E) v := by
    intro j
    have := hR_mem_oEv σ J v Λ hSD (hX j) hc
    rw [hR_sum_smul_right] at this
    have e : Matrix.mulVec (gramR (Fv F v) σ J X) c j = ∑ i, c i * hR (Fv F v) σ J (X j) (X i) := by
      simp only [Matrix.mulVec, dotProduct, gramR]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]; exact this
  obtain ⟨u, huO, -, hdu⟩ := hu
  have key : c i = u * Matrix.mulVec (gramR (Fv F v) σ J X).adjugate
      (Matrix.mulVec (gramR (Fv F v) σ J X) c) i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, ← mul_assoc, mul_comm u, hdu, one_mul]
  rw [key]
  refine oEv_mul v huO ?_
  simp only [Matrix.mulVec, dotProduct]
  exact oEv_sum v _ _ fun j _ => oEv_mul v (adj_int v _ hGi i j) (hGc j)

def IsoW (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ T : Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E),
    (∃ u ∈ OEv (E := E) v, T.det ∈ OEv (E := E) v ∧ T.det * u = 1) ∧
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
      ∃ w ∈ latLoc (E := E) v Λ, gramR (Fv F v) σ J (augT v X w) = T

theorem isoExt_of (a : ℕ) (Y : TupV (E := E) v n a) (hW : IsoW σ J ψ v Λ a Y) : IsoExt σ J ψ v Λ a Y := by
  intro hG
  obtain ⟨T, hTu, h⟩ := hW hG
  refine ⟨T, hTu, fun X hX hXY => ?_⟩
  obtain ⟨w, hw, hg⟩ := h X hX hXY
  refine ⟨w, uniPrim σ J v Λ hG.2.2.1 _ (fun i => ?_) (by rw [hg]; exact hTu), hg⟩
  induction i using Fin.lastCases with
  | last => simp [augT]; exact hw
  | cast j => rw [augT_castSucc]; exact hX.1 j

end PI.OmVd
end
end
