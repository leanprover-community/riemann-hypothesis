import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLatti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrthogonalProjCommComplementUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubspaceRingOfIntegers

section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite := by
  first | exact @GlobalTheory.StabFin.stab_finite | exact GlobalTheory.StabFin.stab_finite | (intros; apply GlobalTheory.StabFin.stab_finite <;> assumption)
end

section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  first | exact @GlobalTheory.FrameSpanLat.inf_span_eq | exact GlobalTheory.FrameSpanLat.inf_span_eq | (intros; apply GlobalTheory.FrameSpanLat.inf_span_eq <;> assumption)
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameProj

set_option maxHeartbeats 1600000 in
open GlobalTheory.ThetaMove.CommonRef in
theorem lattice_between_parts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel Λ₀ hΛ₀
  have hU : ∀ y ∈ Xplus F ⊔ Xplus F', y ∈ orth (VS D) (Xplus F ⊔ Xplus F') → y = 0 := by
    intro y hyU hyW
    by_contra hy
    have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hZ hG y hyW hy
    have h0 : (VS D).hT y y = 0 := (mem_orth_iff _ y).1 hyW y hyU
    rw [h0, map_zero] at hpos
    exact lt_irrefl _ hpos
  have hdet := gram_det_isUnit _ hU
  have hcomm : ∀ p : PlF D, ∀ h ∈ (FP p).UW0, ∀ y,
      projP Z p (Xplus F ⊔ Xplus F') (h y) = h (projP Z p (Xplus F ⊔ Xplus F') y) :=
    fun p h hh y => localOrthogonalProj_comm_complementUnitary Z p F F' (FP p) (hB p).1 (hB p).2.1 h hh y
  generalize Xplus F ⊔ Xplus F' = U at hU hdet hcomm ⊢
  obtain ⟨N, hN, hNmem⟩ := exists_nat_smul_le (full_of_span hΛ₀.span_eq_top)
    (hΛ₀.fg.map ((proj U).restrictScalars (𝓞 D.host.E)))
  have hcast : ∀ v : (VS D).V, (N : D.host.E) • v = (N : 𝓞 D.host.E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  obtain ⟨Q, hQ⟩ : ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, Q = (N : D.host.E) • proj U := ⟨_, rfl⟩
  have hQx : ∀ x, Q x = (N : D.host.E) • proj U x := fun x => by rw [hQ]; rfl
  have hQ₀ : Λ₀.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Λ₀ := by
    rintro _ ⟨x, hx, rfl⟩
    show Q x ∈ Λ₀
    rw [hQx, hcast]
    exact hNmem _ ⟨x, hx, rfl⟩
  refine ⟨N, hN, ?_⟩
  intro Λ hΛ hloc
  have hQp : ∀ p : PlF D, ∀ x, baseChange₂ D p (Q x) = ((N : (D.s.atP p).Ep) • projP Z p U) (baseChange₂ D p x) := by
    intro p x
    rw [hQx, LinearMap.smul_apply, baseChange_smul₂, baseChangeAt_proj Z p, map_natCast]
  have hlat' : Submodule.IsLattice D.host.E (Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E))) :=
    ⟨hΛ.fg.sup (hΛ.fg.map _), top_le_iff.1 (hΛ.span_eq_top ▸ Submodule.span_mono (by
      intro y hy; exact Submodule.mem_sup_left hy))⟩
  have heq : Λ ⊔ Λ.map (Q.restrictScalars (𝓞 D.host.E)) = Λ := by
    refine ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ hlat' hΛ).2 fun p => ?_
    rw [localLattice_sup, sup_eq_left, localLattice_map Z p Q _ (hQp p)]
    obtain ⟨h, hh, himg⟩ := hloc p
    obtain ⟨Qp, hQpdef⟩ : ∃ Qp : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p, Qp = (N : (D.s.atP p).Ep) • projP Z p U :=
      ⟨_, rfl⟩
    rw [← hQpdef]
    have hc : ∀ y, Qp (h y) = h (Qp y) := by
      intro y
      rw [hQpdef, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hcomm p h hh y]
    have hL : (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O) ≤ lattice₂ D Z.M p Λ₀ :=
      calc (lattice₂ D Z.M p Λ₀).map (Qp.restrictScalars (Z.M p).L.O)
          = lattice₂ D Z.M p (Λ₀.map (Q.restrictScalars (𝓞 D.host.E))) :=
            (localLattice_map Z p Q Qp (fun x => hQpdef ▸ hQp p x) Λ₀).symm
        _ ≤ lattice₂ D Z.M p Λ₀ := localLattice_mono Z p hQ₀
    have := img_map_le Z p Qp h hc _ hL
    rwa [himg] at this
  have key : ∀ y ∈ Λ, Q y ∈ Λ := fun y hy => by
    rw [← heq]
    exact Submodule.mem_sup_right ⟨y, hy, rfl⟩
  intro x hx
  refine Submodule.mem_sup.2 ⟨Q x, ⟨key x hx, ?_⟩, (N : D.host.E) • x - Q x, ⟨?_, ?_⟩, add_sub_cancel _ _⟩
  · show Q x ∈ U
    rw [hQx]
    exact U.smul_mem _ (proj_mem U x)
  · refine Λ.sub_mem ?_ (key x hx)
    rw [hcast]
    exact Λ.smul_mem _ hx
  · show (N : D.host.E) • x - Q x ∈ orth (VS D) U
    rw [hQx, ← smul_sub]
    exact Submodule.smul_mem _ _ (sub_proj_mem_orth U hdet x)

end GlobalTheory.FrameProj
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitLattice_between_frameAndComplementParts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ N : ℕ, 0 < N ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')) := by
  atlas_forward_decl GlobalTheory.FrameProj.lattice_between_parts
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecompOrth

variable {D : D7}

theorem mem_orth_of_basis {n : ℕ} (U : Submodule D.host.E (VS D).V)
    (b : Module.Basis (Fin n) D.host.E U) (y : (VS D).V)
    (hy : ∀ i, (VS D).hT (b i : (VS D).V) y = 0) : y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  rw [hu', map_sum]
  simp [hy]

theorem exists_decomp (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (x : (VS D).V) : ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b := by
  let b := Module.finBasis D.host.E U
  let L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
    LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun hy i
    have hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U := ⟨y.2, mem_orth_of_basis U b y hy'⟩
    rw [hU] at hmem
    exact Subtype.ext ((Submodule.mem_bot _).1 hmem)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨y, hy⟩ := hsurj (fun i => (VS D).hT (b i : (VS D).V) x)
  refine ⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩
  have := congrFun hy i
  simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [map_sub, this, sub_self]

theorem gram_det_ne_zero {n : ℕ} (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (b : Module.Basis (Fin n) D.host.E U) :
    (Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V)).det ≠ 0 := by
  intro h
  obtain ⟨α, hα0, hα⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hα0
  have hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0 := by
    intro i
    have := congrFun hα i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Submodule.coe_sum, map_sum]
    simpa [mul_comm] using this
  have hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U :=
    ⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩
  rw [hU, Submodule.mem_bot] at hmem
  have h0 : ∑ j, α j • b j = 0 := Subtype.ext hmem
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j

end GlobalTheory.DecompOrth

namespace GlobalTheory.DecompOrth

variable {D : D7}

noncomputable def formLeft (Z : LocDat D) (p : PlF D) (w : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun v := LocFacts₂ Z.M p v w
  map_add' x y := (locH Z p).h_add_left x y w
  map_smul' a x := (locH Z p).h_smul_left a x w

theorem formLeft_apply (Z : LocDat D) (p : PlF D) (w v : Vp D p) :
    formLeft Z p w v = LocFacts₂ Z.M p v w := rfl

theorem eq_zero_of_local_orth (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (Z : LocDat D) (p : PlF D) (v : Vp D p)
    (hv : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)))
    (horth : ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) : v = 0 := by
  let b := Module.finBasis D.host.E U
  have hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤
      Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hu', map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [baseChange_smul₂]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)
  set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef
  set A := G.map (D.s.atP p).ιE with hA
  have hAβ : Matrix.mulVec A β = 0 := by
    funext i
    have h1 := horth (b i) (b i).2
    have h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) =
        formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) := rfl
    rw [h2, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1
    simp only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simpa [mul_comm] using h1
  have hdet : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _
  have hβ : β = 0 := by
    have := congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  simp [hβ]

end GlobalTheory.DecompOrth

theorem GlobalTheory.decomp_orth_complement : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 :=
  fun _ U hU => ⟨GlobalTheory.DecompOrth.exists_decomp U hU,
    fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_decomposition_local_nondegenerate : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 := by
  atlas_forward_decl GlobalTheory.decomp_orth_complement
end

section
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.OrthLoc

variable {D : D7}

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x y z : Vp D p) :
    LocFacts₂ Z.M p (x + y) z = LocFacts₂ Z.M p x z + LocFacts₂ Z.M p y z := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x z : Vp D p) :
    LocFacts₂ Z.M p (c • x) z = c * LocFacts₂ Z.M p x z := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def orthP (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule (D.s.atP p).Ep (Vp D p) where
  carrier := {v | ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0}
  zero_mem' := by intro u _; simp [LocFacts₂]
  add_mem' := by intro a b ha hb u hu; rw [localForm_add_left, ha u hu, hb u hu, add_zero]
  smul_mem' := by intro c a ha u hu; rw [localForm_smul_left, ha u hu, mul_zero]

theorem span_orth_le (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ≤ orthP Z p U := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩ u hu
  have ha' : (VS D).hT u a = 0 := by
    have ha2 : a ∈ orth (VS D) U := ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at ha2
    exact ha2 u hu
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, ha']

theorem mem_localLattice_inf_orthogonal : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V),
    (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) →
    (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) →
      (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) →
    ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ →
      (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  intro D Z U hdec huniq Λ hΛ p t ht horth
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) U) hΛ.fg
  have hmem : t ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) : Set (Vp D p)) := by
    rw [hsat]
    refine ⟨ht, ?_⟩
    have htop : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) = ⊤ := by
      rw [eq_top_iff, ← span_baseChange_eq_top (D := D) p, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
      rw [map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨b, hb, rfl⟩)
    have ht' : t ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) := htop ▸ Submodule.mem_top
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ht'
    have hβ0 : β = 0 := by
      apply huniq p β hβ
      have e : β = t - α := by rw [← hαβ]; abel
      have hto : t ∈ orthP Z p U := horth
      have h2 := (orthP Z p U).sub_mem hto (span_orth_le Z p U hα)
      rw [← e] at h2
      exact h2
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exact hmem

end GlobalTheory.Unfold.OrthLoc
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V), (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) → (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ → (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  atlas_forward_decl GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal
end

section
open NumberField

namespace GlobalTheory.NatSmulMemOfSpan

theorem exists_nat_mul_eq_coe {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (m : K) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y.natAbs : K) * c) := by
    have hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hint
    · have h2 : ((y.natAbs : ℤ) : K) = -(y : K) := by
        have : (y.natAbs : ℤ) = -y := by omega
        rw [this, Int.cast_neg]
      rw [hc, h2, neg_mul]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩

theorem exists_nat_smul_mem_of_mem_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span K (Λ : Set V)) : ∃ n : ℕ, 0 < n ∧ (n : K) • v ∈ Λ := by
  have key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ := fun a w hw => by
    rw [algebraMap_smul]; exact Λ.smul_mem a hw
  have keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ := fun m w hw => by
    simpa using key (m : 𝓞 K) w hw
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]
    rw [this]
    exact Λ.add_mem (keyN n _ hx) (keyN m _ hy)
  | smul c x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_coe c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x) := by
      rw [ha, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact key a _ hx

theorem exists_nat_smul_mem {D : Formalism.BasicNotions.D7} (Λ : GlobalTheory.Unfold.LV D)
    (hΛ : Submodule.IsLattice ((Formalism.BasicNotions.D7.host D).E) Λ)
    (v : Formalism.BasicNotions.HSpace.V (Formalism.MainNotions.S.VS D)) :
    ∃ n : ℕ, 0 < n ∧ (n : (Formalism.BasicNotions.D7.host D).E) • v ∈ Λ :=
  exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end GlobalTheory.NatSmulMemOfSpan
end

section
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompScale

variable {D : D7}

theorem mem_range_of_int {x : D.host.E} (h : IsIntegral ℤ x) : x ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
  ⟨⟨x, h⟩, rfl⟩

theorem exists_nat_mul (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ (n : D.host.E) * z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, mem_range_of_int ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : D.host.E) * z = y • z := by
      rw [zsmul_eq_mul]; congr 1
      have e : ((y : ℤ) : D.host.E) = (((y.natAbs : ℕ) : ℤ) : D.host.E) := by rw [← h]
      rw [e, Int.cast_natCast]
    rw [this]; exact hy
  · have : ((y.natAbs : ℕ) : D.host.E) * z = -(y • z) := by
      rw [zsmul_eq_mul, ← neg_mul]; congr 1
      have e : ((y : ℤ) : D.host.E) = ((-((y.natAbs : ℕ) : ℤ) : ℤ) : D.host.E) := by rw [← h]
      rw [e, Int.cast_neg, Int.cast_natCast, neg_neg]
    rw [this]; exact hy.neg

theorem range_mul {a b : D.host.E} (ha : a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E))
    (hb : b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : a * b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x * y, map_mul _ _ _⟩

theorem natCast_mem (n : ℕ) : (n : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := ⟨n, map_natCast _ _⟩

theorem exists_nat_mul_fin {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : D.host.E) * f i ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  choose m hm0 hm using fun i => exists_nat_mul (D := D) (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i), Nat.cast_mul, mul_comm ((m i : ℕ) : D.host.E), mul_assoc]
  exact range_mul (natCast_mem _) (hm i)

theorem iota_mem_O (Z : LocDat D) (p : PlF D) (o : 𝓞 D.host.E) :
    (D.s.atP p).ιE (o : D.host.E) ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def]
  exact ((NumberField.RingOfIntegers.isIntegral_coe o).map ((D.s.atP p).ιE.toIntAlgHom)).tower_top

theorem iota_mem_O' (Z : LocDat D) (p : PlF D) {z : D.host.E}
    (h : z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : (D.s.atP p).ιE z ∈ (Z.M p).L.O := by
  obtain ⟨o, rfl⟩ := h; exact iota_mem_O Z p o

open ValuativeRel in
theorem cj_mem (Z : LocDat D) (p : PlF D) {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (Z.M p).L.cj x ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def] at *
  exact hx.map (((Z.M p).L.cj : (D.s.atP p).Ep →ₐ[(D.s.atP p).Fp] (D.s.atP p).Ep).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem complement_unitary_preserves_form {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ x y, LocFacts₂ Z.M p (g x) (g y) = LocFacts₂ Z.M p x y := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => exact fun _ _ => rfl
  | mul x y _ _ hx hy =>
    intro a b
    change LocFacts₂ Z.M p (x (y a)) (x (y b)) = _
    rw [hx, hy]
  | inv x _ hx =>
    intro a b
    change LocFacts₂ Z.M p (x.symm a) (x.symm b) = _
    rw [← hx, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x x' y : Vp D p) :
    LocFacts₂ Z.M p (x + x') y = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x' y := (locH Z p).h_add_left x x' y

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (a : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ Z.M p (a • x) y = a * LocFacts₂ Z.M p x y := (locH Z p).h_smul_left a x y

theorem localForm_zero_left (Z : LocDat D) (p : PlF D) (y : Vp D p) : LocFacts₂ Z.M p 0 y = 0 := by
  simp [LocFacts₂]

theorem localForm_sub_left (Z : LocDat D) (p : PlF D) (x x' y : Vp D p) :
    LocFacts₂ Z.M p (x - x') y = LocFacts₂ Z.M p x y - LocFacts₂ Z.M p x' y := by
  have h := localForm_add_left Z p (x - x') x' y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem localForm_smul_right₂ (Z : LocDat D) (p : PlF D) (a : (D.s.atP p).Ep) (x y : Vp D p) :
    LocFacts₂ Z.M p x (a • y) = (Z.M p).L.cj a * LocFacts₂ Z.M p x y := by
  have h1 := (locH Z p).h_herm (a • y) x
  have h2 := (locH Z p).h_herm y x
  change LocFacts₂ Z.M p x (a • y) = (Z.M p).L.cj (LocFacts₂ Z.M p (a • y) x) at h1
  change LocFacts₂ Z.M p x y = (Z.M p).L.cj (LocFacts₂ Z.M p y x) at h2
  rw [h1, localForm_smul_left, map_mul, ← h2]

theorem localForm_add_right₂ (Z : LocDat D) (p : PlF D) (x y y' : Vp D p) :
    LocFacts₂ Z.M p x (y + y') = LocFacts₂ Z.M p x y + LocFacts₂ Z.M p x y' := by
  have h1 := (locH Z p).h_herm (y + y') x
  have h2 := (locH Z p).h_herm y x
  have h3 := (locH Z p).h_herm y' x
  change LocFacts₂ Z.M p x (y + y') = (Z.M p).L.cj (LocFacts₂ Z.M p (y + y') x) at h1
  change LocFacts₂ Z.M p x y = (Z.M p).L.cj (LocFacts₂ Z.M p y x) at h2
  change LocFacts₂ Z.M p x y' = (Z.M p).L.cj (LocFacts₂ Z.M p y' x) at h3
  rw [h1, localForm_add_left, map_add, ← h2, ← h3]

theorem localForm_zero_right₂ (Z : LocDat D) (p : PlF D) (x : Vp D p) : LocFacts₂ Z.M p x 0 = 0 := by
  simp [LocFacts₂]

theorem mem_of_loc (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ := by
  have := ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) (LatLoc.isLattice_map _ _ hΛ)).1
    (LatLoc.cE D x)).2 (fun p => by rw [← LatLoc.baseChange_eq, ← LatLoc.localLattice_eq]; exact h p)
  obtain ⟨x', hx', he⟩ := Submodule.mem_map.1 this
  have : x' = x := (LatLoc.cE D).injective he
  rwa [this] at hx'

theorem exists_nat_smul_mem (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) (v : (VS D).V) :
    ∃ n : ℕ, 0 < n ∧ (n : D.host.E) • v ∈ Λ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem
  | exact @_root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMemOfSpan.exists_nat_smul_mem ..)

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}

theorem mem_int_of_loc (Z : LocDat D) (z : D.host.E) (hz : ∀ p, (D.s.atP p).ιE z ∈ (Z.M p).L.O) :
    z ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  let Λ1 : Submodule (𝓞 D.host.E) (Fin 1 → D.host.E) := Submodule.span (𝓞 D.host.E) {fun _ => (1 : D.host.E)}
  have h1 : (fun _ : Fin 1 => (1 : D.host.E)) ∈ Λ1 := Submodule.mem_span_singleton_self _
  have hL : Submodule.IsLattice D.host.E Λ1 := by
    refine ⟨Submodule.fg_span_singleton _, ?_⟩
    rw [eq_top_iff]; intro v _
    have : v = v 0 • (fun _ : Fin 1 => (1 : D.host.E)) := by funext i; fin_cases i; simp
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have key := ((GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) 1 Λ1 hL).1 (fun _ => z)).2 (fun p => by
    have hg : (GlobalTheory.HL.placesOf Z).bc p (fun _ : Fin 1 => (1 : D.host.E)) ∈ (GlobalTheory.HL.placesOf Z).lat p Λ1 :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have e : (GlobalTheory.HL.placesOf Z).bc p (fun _ : Fin 1 => z) = (⟨(D.s.atP p).ιE z, hz p⟩ : ((GlobalTheory.HL.placesOf Z).L p).O) •
        (GlobalTheory.HL.placesOf Z).bc p (fun _ : Fin 1 => (1 : D.host.E)) := by
      funext i
      change (D.s.atP p).ιE z = (D.s.atP p).ιE z * (D.s.atP p).ιE 1
      rw [map_one, mul_one]
    rw [e]; exact Submodule.smul_mem _ _ hg)
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 key
  refine ⟨o, ?_⟩
  have := congrFun ho 0
  simpa [Algebra.smul_def] using this

theorem range_add {a b : D.host.E} (ha : a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E))
    (hb : b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) : a + b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact ⟨x + y, map_add _ _ _⟩

theorem star_mem (o : 𝓞 D.host.E) : star (o : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
  mem_range_of_int ((NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd D.host.E).toIntAlgHom)

theorem localForm_sum_left (Z : LocDat D) (p : PlF D) {ι : Type} (s : Finset ι) (f : ι → Vp D p) (z : Vp D p) :
    LocFacts₂ Z.M p (∑ j ∈ s, f j) z = ∑ j ∈ s, LocFacts₂ Z.M p (f j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, localForm_add_left, ih]

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}

theorem scale_part : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ d : ℕ, 0 < d ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
  intro D X Y u u' F F' w _ _ Z FP _ _ Λ₀ h0
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.1 h0.fg
  haveI : Fintype S := hSfin.fintype
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_fin (D := D) (fun ij : S × S => (VS D).hT ij.1 ij.2)
  have hzero : (0 : D.host.E) ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := ⟨0, map_zero _⟩

  have hint1 : ∀ a ∈ S, ∀ b ∈ Λ₀, (d : D.host.E) * (VS D).hT a b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
    intro a ha b hb
    rw [← hSspan] at hb
    induction hb using Submodule.span_induction with
    | mem b hb => exact hd (⟨a, ha⟩, ⟨b, hb⟩)
    | zero => rw [map_zero, mul_zero]; exact hzero
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact range_add hx hy
    | smul o x _ hx =>
      rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul, mul_left_comm]
      exact range_mul ⟨o, rfl⟩ hx
  have hint0 : ∀ a ∈ Λ₀, ∀ b ∈ Λ₀, (d : D.host.E) * (VS D).hT a b ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) := by
    intro a ha b hb
    rw [← hSspan] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hint1 a ha b hb
    | zero => rw [map_zero, LinearMap.zero_apply, mul_zero]; exact hzero
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, mul_add]; exact range_add hx hy
    | smul o x _ hx =>
      rw [← algebraMap_smul D.host.E o x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mul_left_comm]
      exact range_mul (star_mem o) hx
  refine ⟨d, hd0, fun Λ _ hloc x hx y hy => mem_int_of_loc Z _ fun p => ?_⟩
  obtain ⟨h, hh, himg⟩ := hloc p
  have hun := complement_unitary_preserves_form (FP p) hh
  have hxp : baseChange₂ D p x ∈ LocNG.img h (lattice₂ D Z.M p Λ₀) := by rw [himg]; exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hyp : baseChange₂ D p y ∈ LocNG.img h (lattice₂ D Z.M p Λ₀) := by rw [himg]; exact Submodule.subset_span ⟨y, hy, rfl⟩
  obtain ⟨x₀, hx₀, hxe⟩ := Submodule.mem_map.1 hxp
  obtain ⟨y₀, hy₀, hye⟩ := Submodule.mem_map.1 hyp
  have hform : ∀ a b, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p b) = (D.s.atP p).ιE ((VS D).hT b a) :=
    fun a b => baseChangeAt_form Z.M p (Z.hcj p) a b
  have e : (D.s.atP p).ιE ((d : D.host.E) * (VS D).hT x y) = (d : (D.s.atP p).Ep) * LocFacts₂ Z.M p y₀ x₀ := by
    rw [map_mul, map_natCast, ← hform, ← hye, ← hxe]
    exact congrArg _ (hun y₀ x₀)
  rw [e]

  have hloc0 : ∀ a ∈ lattice₂ D Z.M p Λ₀, ∀ b ∈ lattice₂ D Z.M p Λ₀, (d : (D.s.atP p).Ep) * LocFacts₂ Z.M p a b ∈ (Z.M p).L.O := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨b, hb, rfl⟩ := hb
        rw [hform, ← map_natCast (D.s.atP p).ιE, ← map_mul]
        exact iota_mem_O' Z p (hint0 b hb a ha)
      | zero => rw [localForm_zero_right₂, mul_zero]; exact (Z.M p).L.O.zero_mem
      | add x y _ _ hx hy => rw [localForm_add_right₂, mul_add]; exact (Z.M p).L.O.add_mem hx hy
      | smul o x _ hx =>
        rw [Subring.smul_def, localForm_smul_right₂, mul_left_comm]
        exact (Z.M p).L.O.mul_mem (cj_mem Z p o.2) hx
    | zero => rw [localForm_zero_left, mul_zero]; exact (Z.M p).L.O.zero_mem
    | add x y _ _ hx hy => rw [localForm_add_left, mul_add]; exact (Z.M p).L.O.add_mem hx hy
    | smul o x _ hx =>
      rw [Subring.smul_def, localForm_smul_left, mul_left_comm]
      exact (Z.M p).L.O.mul_mem o.2 hx
  exact hloc0 y₀ hy₀ x₀ hx₀

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

variable {D : D7}

set_option maxHeartbeats 2000000 in

theorem dual_part : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ c : ℕ, 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  set U := Xplus F ⊔ Xplus F' with hU
  have memW : ∀ x, x ∈ orth (VS D) U ↔ ∀ v ∈ U, (VS D).hT v x = 0 := fun x => by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdef : ∀ x ∈ orth (VS D) U, (VS D).hT x x = 0 → x = 0 := fun x hx h => by
    by_contra hne
    have := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hw hG x hx hne
    rw [h, map_zero] at this; exact lt_irrefl _ this
  have hUW : U ⊓ orth (VS D) U = ⊥ := by
    rw [eq_bot_iff]; rintro x ⟨hxU, hxW⟩
    exact (Submodule.mem_bot _).2 (hdef x hxW ((memW x).1 hxW x hxU))
  obtain ⟨hdec, hloc0⟩ := GlobalTheory.T.orthogonal_decomposition_local_nondegenerate D U hUW

  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent D.host.E
    ((Λ₀ ⊓ toO (VS D) (orth (VS D) U) : LV D) : Set (VS D).V)
  have hspanW : Submodule.span D.host.E b = orth (VS D) U := by
    rw [hbspan]; apply le_antisymm
    · rw [Submodule.span_le]; exact fun x hx => hx.2
    · intro x hx
      obtain ⟨n, hn, hnx⟩ := exists_nat_smul_mem Λ₀ h0 x
      have hmem : (n : D.host.E) • x ∈ Submodule.span D.host.E
          ((Λ₀ ⊓ toO (VS D) (orth (VS D) U) : LV D) : Set (VS D).V) :=
        Submodule.subset_span ⟨hnx, (orth (VS D) U).smul_mem _ hx⟩
      have hn' : (n : D.host.E) ≠ 0 := by exact_mod_cast hn.ne'
      have := Submodule.smul_mem _ ((n : D.host.E)⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ hn', one_smul] at this
  haveI : Finite b := hli.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hvΛ : ∀ i : b, (i : (VS D).V) ∈ Λ₀ := fun i => (hbs i.2).1
  have hvW : ∀ i : b, (i : (VS D).V) ∈ orth (VS D) U := fun i => (hbs i.2).2
  let B : Matrix b b D.host.E := fun i j => (VS D).hT (j : (VS D).V) (i : (VS D).V)
  have hBdet : B.det ≠ 0 := by
    intro hd
    obtain ⟨α, hα0, hα⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hα0
    have hj : ∀ j : b, (VS D).hT (j : (VS D).V) (∑ i, α i • (i : (VS D).V)) = 0 := by
      intro j
      have := congrFun hα j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, B] at this
      rw [map_sum]
      simpa [map_smul, smul_eq_mul, mul_comm] using this
    have hxW : (∑ i, α i • (i : (VS D).V)) ∈ orth (VS D) U :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvW i)
    have hxx : ∀ x', (∀ j : b, (VS D).hT (j : (VS D).V) x' = 0) →
        (VS D).hT (∑ i, α i • (i : (VS D).V)) x' = 0 := by
      intro x' hx'
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx' i, smul_zero]
    have h0' := hdef _ hxW (hxx _ hj)
    funext i
    exact Fintype.linearIndependent_iff.1 hli α h0' i
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hBdet
  obtain ⟨c, hc0, hc⟩ := exists_nat_mul_fin (D := D) (fun ij : b × b => B⁻¹ ij.1 ij.2)
  refine ⟨c, hc0, fun Λ hΛ hloc y hyW hy => mem_of_loc Z Λ hΛ _ fun p => ?_⟩
  obtain ⟨h, hh, himg⟩ := hloc p
  have hfix : ∀ x ∈ U, h (baseChange₂ D p x) = baseChange₂ D p x := fun x hx =>
    GlobalTheory.FrameSpanLat.fix_span F F' Z FP hB hR p hh hx
  have hun := complement_unitary_preserves_form (FP p) hh
  have hform : ∀ a b, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p b) = (D.s.atP p).ιE ((VS D).hT b a) :=
    fun a b => baseChangeAt_form Z.M p (Z.hcj p) a b
  have horthW : ∀ a ∈ orth (VS D) U, ∀ x ∈ U, LocFacts₂ Z.M p (baseChange₂ D p a) (baseChange₂ D p x) = 0 := fun a ha x hx => by
    rw [hform, (memW a).1 ha x hx, map_zero]
  have hy'o : ∀ x ∈ U, LocFacts₂ Z.M p (h.symm (baseChange₂ D p y)) (baseChange₂ D p x) = 0 := fun x hx => by
    rw [← hun, LinearEquiv.apply_symm_apply, hfix x hx]; exact horthW y hyW x hx
  let Sb := Submodule.span (D.s.atP p).Ep (Set.range fun i : b => baseChange₂ D p (i : (VS D).V))
  let SU := Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V))
  have hSbo : ∀ s ∈ Sb, ∀ x ∈ U, LocFacts₂ Z.M p s (baseChange₂ D p x) = 0 := by
    intro s hs x hx
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨i, rfl⟩ := hs; exact horthW _ (hvW i) x hx
    | zero => exact localForm_zero_left Z p _
    | add a a' _ _ ha ha' => rw [localForm_add_left, ha, ha', add_zero]
    | smul e a _ ha => rw [localForm_smul_left, ha, mul_zero]
  have hbcW : ∀ a ∈ orth (VS D) U, baseChange₂ D p a ∈ Sb := by
    intro a ha
    rw [← hspanW] at ha
    have ha' : a ∈ Submodule.span D.host.E (Set.range (fun i : b => (i : (VS D).V))) := by
      rwa [Subtype.range_coe]
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 ha'
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : ∀ z : Vp D p, z ∈ Sb ⊔ SU := by
    intro z
    have : z ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, ha, b', hb', rfl⟩ := hdec x
    rw [map_add]
    exact Submodule.add_mem_sup (hbcW a ha) (Submodule.subset_span ⟨b', hb', rfl⟩)
  have hy'Sb : h.symm (baseChange₂ D p y) ∈ Sb := by
    obtain ⟨s1, hs1, s2, hs2, hsum⟩ := Submodule.mem_sup.1 (htop (h.symm (baseChange₂ D p y)))
    have hs2o : ∀ x ∈ U, LocFacts₂ Z.M p s2 (baseChange₂ D p x) = 0 := fun x hx => by
      have e2 : s2 = h.symm (baseChange₂ D p y) - s1 := by rw [← hsum]; abel
      rw [e2, localForm_sub_left, hy'o x hx, hSbo s1 hs1 x hx, sub_zero]
    have := hloc0 Z p s2 hs2 hs2o
    rw [← hsum, this, add_zero]; exact hs1
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hy'Sb

  have hK : ∀ i : b, LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))) ∈ (Z.M p).L.O := by
    intro i
    have ht : h (baseChange₂ D p (i : (VS D).V)) ∈ lattice₂ D Z.M p Λ := by
      rw [← himg]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, hvΛ i, rfl⟩)
    have hto : ∀ x ∈ U, LocFacts₂ Z.M p (h (baseChange₂ D p (i : (VS D).V))) (baseChange₂ D p x) = 0 := fun x hx => by
      rw [← hfix x hx, hun]; exact horthW _ (hvW i) x hx
    have htK := GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part D Z U hdec (hloc0 Z) Λ hΛ p _ ht hto
    generalize h (baseChange₂ D p (i : (VS D).V)) = t at htK
    induction htK using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨k, hk, rfl⟩ := hs
      rw [hform]; exact iota_mem_O' Z p (hy k hk)
    | zero => rw [localForm_zero_right₂]; exact (Z.M p).L.O.zero_mem
    | add a a' _ _ ha ha' => rw [localForm_add_right₂]; exact (Z.M p).L.O.add_mem ha ha'
    | smul o a _ ha =>
      rw [Subring.smul_def, localForm_smul_right₂]
      exact (Z.M p).L.O.mul_mem (cj_mem Z p o.2) ha
  have hrel : (fun i : b => LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V)))) =
      Matrix.vecMul β (B.map (D.s.atP p).ιE) := by
    funext i
    have e1 : LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))) =
        LocFacts₂ Z.M p (h.symm (baseChange₂ D p y)) (baseChange₂ D p (i : (VS D).V)) := by
      have := hun (h.symm (baseChange₂ D p y)) (baseChange₂ D p (i : (VS D).V))
      rwa [LinearEquiv.apply_symm_apply] at this
    rw [e1, ← hβ, localForm_sum_left]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [localForm_smul_left, hform]
  have hβeq : β = Matrix.vecMul (fun i : b => LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (i : (VS D).V))))
      (B⁻¹.map (D.s.atP p).ιE) := by
    rw [hrel, Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hBu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
  have hmem : ∀ j : b, (c : (D.s.atP p).Ep) * β j ∈ (Z.M p).L.O := by
    intro j
    have e : (c : (D.s.atP p).Ep) * β j = ∑ k : b, LocFacts₂ Z.M p (baseChange₂ D p y) (h (baseChange₂ D p (k : (VS D).V))) *
        (D.s.atP p).ιE ((c : D.host.E) * B⁻¹ k j) := by
      conv_lhs => rw [hβeq]
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_mul, map_natCast]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact Subring.sum_mem _ fun k _ => (Z.M p).L.O.mul_mem (hK k) (iota_mem_O' Z p (hc (k, j)))
  have hcy' : (c : (D.s.atP p).Ep) • h.symm (baseChange₂ D p y) ∈ lattice₂ D Z.M p Λ₀ := by
    rw [← hβ, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_smul]
    have e : ((c : (D.s.atP p).Ep) * β j) • baseChange₂ D p (j : (VS D).V) =
        (⟨_, hmem j⟩ : (Z.M p).L.O) • baseChange₂ D p (j : (VS D).V) := rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hvΛ j, rfl⟩)
  rw [baseChange_smul₂, map_natCast, ← himg, ← LinearEquiv.apply_symm_apply h (baseChange₂ D p y), ← h.map_smul]
  exact Submodule.mem_map_of_mem hcy'

end GlobalTheory.CompScale

namespace GlobalTheory.CompScale

theorem scale_dual : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ d c : ℕ, 0 < d ∧ 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) ∧ ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  obtain ⟨d, hd0, hd⟩ := scale_part D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  obtain ⟨c, hc0, hc⟩ := dual_part D X Y u u' F F' w hw hG Z FP hB hR Λ₀ h0
  exact ⟨d, c, hd0, hc0, fun Λ hΛ hloc => ⟨hd Λ hΛ hloc, hc Λ hΛ hloc⟩⟩

end GlobalTheory.CompScale
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.based_flag_pair_lattice_containment : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ d c : ℕ, 0 < d ∧ 0 < c ∧ ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) ∧ ∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ := by
  atlas_forward_decl GlobalTheory.CompScale.scale_dual
end

section
section
open NumberField

namespace GlobalTheory

theorem hermLat_boundedScaleDual_finite {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (d c : ℕ) (hd : 0 < d) (hc : 0 < c) :
    ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧
      ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
        (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) →
        (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) →
        ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  classical
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.final_traceReal K V h hs hpos
  set e : ℤ := NumberField.discr K with he
  have he0 : e ≠ 0 := NumberField.discr_ne_zero K
  have ecast : ((e.natAbs ^ 2 : ℕ) : K) = ((e : K)) * (e : K) := by
    have h0 : ((e.natAbs ^ 2 : ℕ) : ℤ) = e * e := by rw [Nat.cast_pow, Int.natAbs_sq, sq]
    rw [← Int.cast_natCast, h0, Int.cast_mul]
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) ∧
    (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M)}
  obtain ⟨s, hs1, hs2⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.final_shortVectors
    Formalism.HermitianLatticesTheory.final_finIntermediate Formalism.HermitianLatticesTheory.final_isomOfTrace h hpos N ι hι hmul d hd
    (Real.sqrt (((c * e.natAbs ^ 2 : ℕ) : ℝ) ^ N)) S
    (fun M hM x hx y hy => Submodule.mem_one.mpr (hM.2.1 x hx y hy))
    (fun M hM => hlat M hM.1)
    (by
      intro M hM _ _
      apply Formalism.HermitianLatticesTheory.genusCovolBound_covol_le h N ι hι M (c * e.natAbs ^ 2)
        (Nat.mul_pos hc (pow_pos (Int.natAbs_pos.mpr he0) 2))
      have hdual : ∀ y, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
          ∀ x ∈ M, h x ((e : K) • y) ∈ Set.range (algebraMap (𝓞 K) K) := by
        intro y hy x hx
        rw [LinearMap.map_smul, smul_eq_mul]
        have hm : ((e : ℤ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
          apply Formalism.HermitianLatticesTheory.genusCovolBound_discr
          intro r
          obtain ⟨s, hs'⟩ := hstar r
          obtain ⟨z, hz⟩ := hy (s • x) (M.smul_mem s hx)
          refine ⟨z, ?_⟩
          rw [← hz]
          congr 1
          rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
            starRingEnd_apply, hs', star_star, mul_comm]
        exact Submodule.mem_one.mp hm
      intro y y' hy hy'
      have h1 : (c : K) • ((e : K) • y) ∈ M := hM.2.2 _ (hdual y hy)
      have h2 := hdual y' hy' _ h1
      have key : h ((c : K) • ((e : K) • y)) ((e : K) • y') =
          algebraMap ℚ K ((c * e.natAbs ^ 2 : ℕ) : ℚ) * h y y' := by
        rw [map_natCast, Nat.cast_mul, ecast]
        simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply, star_intCast,
          star_natCast, smul_eq_mul]
        ring
      rw [key] at h2
      obtain ⟨r, hr⟩ := h2
      obtain ⟨z, hz⟩ := Formalism.HermitianLatticesTheory.genusCovolBound_trace_int (K := K) r
      refine ⟨z, ?_⟩
      rw [← hz, hr, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul])
  exact ⟨s, fun M₀ hM₀ => (hs1 M₀ hM₀).1, fun M hL hd' hc' => hs2 M ⟨hL, hd', hc'⟩⟩

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale : ∀ {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) → ∀ (d c : ℕ), 0 < d → 0 < c → ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧ ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) → ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  atlas_forward_decl GlobalTheory.hermLat_boundedScaleDual_finite
end

section
section
open NumberField

namespace GlobalTheory

theorem finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  intro K V _ _ _ _ _ _ M hM N hN
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  let f : V →ₗ[𝓞 K] V := (((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hf : ∀ x, f x = (N : K)⁻¹ • x := fun x => rfl
  have hback : ∀ x : V, f ((N : K) • x) = x := by
    intro x; rw [hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]
  have hsm : ∀ x ∈ M, (N : K) • x ∈ M := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx N
  set D := M.map f with hD
  have hMD : M ≤ D := fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩
  have hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D} := by
    rintro Λ ⟨h1, h2⟩
    exact ⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩
  refine Set.Finite.subset ?_ hsub
  have h1 := Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr (hM.map f)
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      obtain ⟨m, hm, hq⟩ := q.2
      have : (((N : ℤ) • q : D.toAddSubgroup) : V) = m := by
        rw [AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
          smul_smul, mul_inv_cancel₀ hNK, one_smul]
      rw [this]
      exact hm

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattices_between_of_smul_le' : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  atlas_forward_decl GlobalTheory.finite_lattices_between_of_smul_le
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.isCompl_orth_of_definite {E : Type} [Field E] [NumberField E] [StarRing E]
    (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V)
    (hpos : ∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) :
    IsCompl U (orth S U) := by
  have hmem : ∀ v, v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
    intro v
    simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdis : U ⊓ orth S U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxU, hxO⟩
    by_contra hne
    have h0 : S.hT x x = 0 := (hmem x).1 hxO x hxU
    have := hpos x hxO hne
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => S.hT (b i : S.V)
  have hker : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [hmem]
    intro x hx
    have hy' : ∀ i, S.hT (b i : S.V) y = 0 := fun i => congrFun hy i
    have hx' : (⟨x, hx⟩ : U) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have hxs : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
      have := congrArg (Subtype.val) hx'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this
    rw [hxs, map_sum]
    simp [LinearMap.sum_apply, hy']
  have hrk : Module.finrank E S.V ≤ Module.finrank E U + Module.finrank E (orth S U) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    have h3 := Submodule.finrank_mono hker
    omega
  have hcod : U ⊔ orth S U = ⊤ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
    rw [hdis, finrank_bot] at h
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (U ⊔ orth S U)
    omega
  exact ⟨disjoint_iff.2 hdis, codisjoint_iff.2 hcod⟩
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), (∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) → IsCompl U (orth S U) := by
  atlas_forward_decl GlobalTheory.isCompl_orth_of_definite
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthExt

theorem hT_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT u v = 0 := by
  have := hv
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this u hu

theorem hT_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT v u = 0 := by
  have h1 := S.herm.eq u v
  rw [hT_orth_right S U hu hv] at h1
  simpa using h1.symm

theorem extend_isom : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  intro E _ _ _ S U hc g hg
  let e := Submodule.prodEquivOfIsCompl U (orth S U) hc
  let γ : S.V ≃ₗ[E] S.V := (e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e
  have hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V) := fun x => rfl
  have hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V) := fun x => by
    conv_lhs => rw [← e.apply_symm_apply x]
    rfl
  have key : ∀ (a b : U) (c d : ↥(orth S U)),
      S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d := by
    intro a b c d
    simp only [map_add, LinearMap.add_apply]
    rw [GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]
    ring
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro x y
    change S.hT (γ x) (γ y) = S.hT x y
    rw [hγ, hγ, key, hg, ← key, ← hx, ← hx]
  · intro u hu
    rw [hγ]
    have : e.symm u = (⟨u, hu⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩
    rw [this]; simp
  · intro w
    rw [hγ]
    have : e.symm w = (0, w) := Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w
    rw [this]; simp

end GlobalTheory.OrthExt
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  atlas_forward_decl GlobalTheory.OrthExt.extend_isom
end

section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V), Submodule.IsLattice K Λ → ∀ W : Submodule K V, Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.isLattice_comap_subtype_ringOfIntegers | exact GlobalTheory.isLattice_comap_subtype_ringOfIntegers | (intros; apply GlobalTheory.isLattice_comap_subtype_ringOfIntegers <;> assumption)
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatClassFin

theorem fg_of_le_fg {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    {N L : Submodule (𝓞 K) V} (hL : L.FG) (h : N ≤ L) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_of_le_right h]
  rw [← e]; exact h1.map _

theorem frame_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    {r : ℕ} {T : E} (F : LFlag S r T) (a : Fin (r + 1)) : frame F a ∈ Xplus F := by
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  | cast i =>
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.castSucc i) ∈ F.fl.X ⊔ E ∙ F.fl.z
    rw [Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem classes_fin : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D T T' F F' hpos A N d c hN hd hc
  classical
  set U : Submodule D.host.E (VS D).V := Xplus F ⊔ Xplus F' with hUdef
  set W : Submodule D.host.E (VS D).V := orth (VS D) U with hWdef
  have hcompl : IsCompl U W := GlobalTheory.T.isCompl_hermitianOrthogonal_of_totallyPositive (VS D) U hpos
  let hW : ↥W →ₗ⋆[D.host.E] ↥W →ₗ[D.host.E] D.host.E := (VS D).hT.domRestrict₁₂ W W
  have hWs : hW.IsSymm := (VS D).herm.domRestrict W
  have hWp : ∀ x : ↥W, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (hW x x) := fun x hx =>
    hpos x.1 x.2 (fun h => hx (Subtype.ext h))
  obtain ⟨s, hslat, hs⟩ := GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale hW hWs hWp d c hd hc
  let ι : ↥W →ₗ[𝓞 D.host.E] (VS D).V := W.subtype.restrictScalars (𝓞 D.host.E)
  let Mof : Submodule (𝓞 D.host.E) ↥W → LV D := fun L => A ⊔ L.map ι
  let Sset : Set (LV D) :=
    ⋃ L ∈ s, {Λ' | A.FG ∧ L.FG ∧ Mof L ≤ Λ' ∧ ∀ x ∈ Λ', (N : D.host.E) • x ∈ Mof L}
  have hfin : Sset.Finite := by
    refine Set.Finite.biUnion s.finite_toSet fun L _ => ?_
    by_cases hA : A.FG
    · by_cases hL : L.FG
      · refine (GlobalTheory.T.finite_lattices_between_of_smul_le' (Mof L) (hA.sup (hL.map ι)) N hN).subset ?_
        rintro Λ' ⟨-, -, h1, h2⟩
        exact ⟨h1, h2⟩
      · exact Set.finite_empty.subset (by rintro Λ' ⟨-, h, -⟩; exact absurd h hL)
    · exact Set.finite_empty.subset (by rintro Λ' ⟨h, -⟩; exact absurd h hA)
  refine ⟨hfin.toFinset, fun Λ hΛ hAΛ hNΛ hdΛ hcΛ => ?_⟩
  set L' : Submodule (𝓞 D.host.E) ↥W := Λ.comap ι with hL'
  have hL'lat : Submodule.IsLattice D.host.E L' := GlobalTheory.T.isLattice_comap_subspace_ringOfIntegers Λ hΛ W
  have hsc : ∀ x ∈ L', ∀ y ∈ L', (d : D.host.E) * hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E) :=
    fun x hx y hy => hdΛ x.1 hx y.1 hy
  have hdu : ∀ y : ↥W, (∀ x ∈ L', hW x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) →
      (c : D.host.E) • y ∈ L' := by
    intro y hy
    show (c : D.host.E) • (y : (VS D).V) ∈ Λ
    exact hcΛ y.1 y.2 (fun x hx => hy ⟨x, hx.2⟩ hx.1)
  obtain ⟨M₀, hM₀s, g, hg, hgM⟩ := hs L' hL'lat hsc hdu
  have hgiso : ∀ x y : ↥W, (VS D).hT (g x : (VS D).V) (g y : (VS D).V) = (VS D).hT (x : (VS D).V) (y : (VS D).V) :=
    fun x y => hg x y
  obtain ⟨γ, hγi, hγU, hγW⟩ := GlobalTheory.T.exists_isometry_extend_orthogonal_by_identity (VS D) U hcompl g hgiso
  have hγH : γ ∈ H0 F F' :=
    ⟨hγi, fun a => hγU _ (Submodule.mem_sup_left (frame_mem_Xplus F a)),
      fun a => hγU _ (Submodule.mem_sup_right (frame_mem_Xplus F' a))⟩
  have hmem : ∀ x, x ∈ Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ ↔ γ x ∈ Λ := fun x => by
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; rfl
  have hAsub : ∀ a ∈ A, a ∈ Λ ∧ a ∈ U := fun a ha => by
    rw [← hAΛ] at ha; exact ⟨ha.1, ha.2⟩
  refine ⟨Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ, ?_, γ, hγH, by simpa using Formalism.HermitianLatticesTheory.genusBasic_gmap_inv γ⁻¹ Λ⟩
  rw [Set.Finite.mem_toFinset]
  have hAfg : A.FG := by
    rw [← hAΛ]; exact fg_of_le_fg hΛ.fg inf_le_left
  have hWsymm : ∀ w (hw : w ∈ W) (hwΛ : w ∈ Λ), γ.symm w ∈ M₀.map ι := by
    intro w hw hwΛ
    have h1 : (⟨w, hw⟩ : ↥W) ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by rw [hgM]; exact hwΛ
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearEquiv.eq_symm_apply]
    show γ ((g.symm ⟨w, hw⟩ : ↥W) : (VS D).V) = w
    rw [hγW, LinearEquiv.apply_symm_apply]
  refine Set.mem_biUnion hM₀s ⟨hAfg, (hslat M₀ hM₀s).fg, ?_, ?_⟩
  · refine sup_le (fun a ha => ?_) ?_
    · rw [hmem, hγU a (hAsub a ha).2]; exact (hAsub a ha).1
    · rintro _ ⟨m, hm, rfl⟩
      rw [hmem]
      show γ ((m : ↥W) : (VS D).V) ∈ Λ
      rw [hγW]
      have h1 : g m ∈ Formalism.HermitianLatticesTheory.gmap g M₀ := by
        rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]; exact hm
      rw [hgM] at h1
      exact h1
  · intro x hx
    rw [hmem] at hx
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp (hNΛ _ hx)
    have hx' : (N : D.host.E) • x = γ.symm u + γ.symm w := by
      rw [← map_add, huw, map_smul, LinearEquiv.symm_apply_apply]
    have hu' : γ.symm u = u := by
      rw [LinearEquiv.symm_apply_eq]; exact (hγU u hu.2).symm
    rw [hx', hu']
    refine Submodule.add_mem_sup ?_ (hWsymm w hw.2 hw.1)
    rw [← hAΛ]; exact hu

end GlobalTheory.LatClassFin
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T'), (∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x)) → ∀ (A : LV D) (N d c : ℕ), 0 < N → 0 < d → 0 < c → ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = A → (∀ x ∈ Λ, (N : D.host.E) • x ∈ Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') ⊔ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F'))) → (∀ x ∈ Λ, ∀ y ∈ Λ, (d : D.host.E) * (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (∀ y ∈ orth (VS D) (Xplus F ⊔ Xplus F'), (∀ x ∈ Λ ⊓ toO (VS D) (orth (VS D) (Xplus F ⊔ Xplus F')), (VS D).hT x y ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)) → (c : D.host.E) • y ∈ Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  atlas_forward_decl GlobalTheory.LatClassFin.classes_fin
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.ClFin

theorem classes_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hw hG
  refine ⟨GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice D F F' hpos Λ₀ hΛ₀, ?_⟩
  obtain ⟨N, hN, hNs⟩ := GlobalTheory.T.orbitLattice_between_frameAndComplementParts D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨d, c, hd, hc, hdc⟩ := GlobalTheory.T.based_flag_pair_lattice_containment D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale D F F' hpos (Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F')) N d c hN hd hc
  exact ⟨S, fun Λ hΛ hloc => hS Λ hΛ (GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀ Λ hΛ hloc)
    (hNs Λ hΛ hloc) (hdc Λ hΛ hloc).1 (hdc Λ hΛ hloc).2⟩

end GlobalTheory.Unfold.ClFin
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLatticeClasses_finite_localOrbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  atlas_forward_decl GlobalTheory.Unfold.ClFin.classes_finite
end
