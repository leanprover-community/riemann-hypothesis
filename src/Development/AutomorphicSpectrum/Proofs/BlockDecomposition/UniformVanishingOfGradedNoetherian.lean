import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.UV

theorem subsingleton_cokernel_desc_of_span {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} [∀ i, (F i).IsQuasicoherent] [G.IsQuasicoherent]
    [(biproduct F).IsQuasicoherent] (φ : ∀ i, F i ⟶ G) {V : X.Opens} (hV : IsAffineOpen V)
    (h : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) = ⊤) :
    Subsingleton Γ(cokernel (biproduct.desc φ), V) := by
  refine subsingleton_of_forall_eq 0 fun s => ?_
  obtain ⟨t, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app (biproduct.desc φ) hV s
  have hle : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) ≤
      LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) := by
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hy
    have hz : φ i ≫ cokernel.π (biproduct.desc φ) = 0 := by
      rw [← biproduct.ι_desc φ i, Category.assoc, cokernel.condition, comp_zero]
    change (cokernel.π (biproduct.desc φ)).app V ((φ i).app V x) = 0
    rw [GlobalTheory.QCoh.app_app, hz]
    rfl
  have ht : t ∈ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) :=
    hle (h ▸ Submodule.mem_top)
  exact ht

theorem span_range_app_eq_top_of_surjective {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} (φ : ∀ i, F i ⟶ G) (U : X.Opens)
    (h : Function.Surjective ((biproduct.desc φ).app U)) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun s => ?_
  obtain ⟨t, rfl⟩ := h s
  rw [GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum F U t, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ?_⟩)
  refine ⟨(biproduct.π F j).app U t, ?_⟩
  rw [GlobalTheory.QCoh.app_app (biproduct.ι F j), biproduct.ι_desc]

theorem span_range_app_eq_top_of_local : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι]
    {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent →
    ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) →
    ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  intro X ι _ F G hF hG φ hloc U
  classical
  haveI := Fintype.ofFinite ι
  haveI := hF
  haveI := hG
  haveI : (biproduct F).IsQuasicoherent := GroundTheory.Arith.SchemeCoh.isQuasicoherent_biproduct F
  choose W hxW hW using hloc
  have hcov : TopologicalSpace.IsOpenCover (fun x : X => (W x : X.Opens)) := by
    refine eq_top_iff.2 fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  have hzero : IsZero (cokernel (biproduct.desc φ)) :=
    (GlobalTheory.QCoh.isZero_iff_affineCover (fun x : X => (W x : X.Opens)) hcov (fun x => (W x).2)).2
      fun x => subsingleton_cokernel_desc_of_span φ (W x).2 (hW x)
  haveI : Epi (biproduct.desc φ) := Preadditive.epi_of_isZero_cokernel _ hzero
  exact span_range_app_eq_top_of_surjective φ U
    (GlobalTheory.QCoh.surjective_app_of_epi (biproduct.desc φ) U.2)

end GlobalTheory.CompanionTheory.GE.UV
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_sections_all_affines_of_cover : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι] {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent → ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) → ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}

variable (M T) in

def kerι (e : ℕ) : kerSeq M T e ⟶ M e := kernel.ι (T (Fin.last k) e)

theorem kerι_comp (e : ℕ) : kerι M T e ≫ T (Fin.last k) e = 0 :=
  kernel.condition _

theorem kerOps_comp_kerι (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k)
    (e : ℕ) : kerOps hc i e ≫ kerι M T (e + 1) = kerι M T e ≫ T i.castSucc e := by
  simp [kerOps, kerι, kerSeq, kernel.map]

open GlobalTheory.CompanionTheory.GE.KerSeq in

theorem kerOps_gen_bounded : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  intro hG X _ k M T d hM U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  haveI : ∀ e, Module.Finite Γ(X, U) Γ(M e, (U : X.Opens)) := fun e => (hM.coherent e).2 U U.2
  have hcomm : ∀ (i j : Fin (k + 1)) (e : ℕ) (x : Γ(M e, (U : X.Opens))),
      secMap (T j (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) =
        secMap (T i (e + 1)) (U : X.Opens) (secMap (T j e) (U : X.Opens) x) := by
    intro i j e x
    simp only [secMap_comp]
    rw [hM.comm i j e]
  obtain ⟨d', hd'⟩ := hG Γ(X, U) (k + 1) (fun e => Γ(M e, (U : X.Opens)))
    (fun i e => secMap (T i e) (U : X.Opens)) hcomm d
    (fun e he => by
      have h := hM.gen e he U
      rw [eq_top_iff, ← h, Submodule.span_le]
      intro w hw
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.1 hw
      exact Submodule.mem_iSup_of_mem i ⟨z, rfl⟩)
    (fun e => LinearMap.ker (secMap (T (Fin.last k) e) (U : X.Opens)))
    (fun i e => by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : secMap (T (Fin.last k) e) (U : X.Opens) x = 0 := hx
      change secMap (T (Fin.last k) (e + 1)) (U : X.Opens) (secMap (T i e) (U : X.Opens) x) = 0
      rw [hcomm i (Fin.last k) e x, hx', map_zero])
  refine ⟨d', fun e he => ?_⟩

  have hι : ∀ e, Function.Injective (secMap (kerι M T e) (U : X.Opens)) :=
    fun e => kernel_ι_app_injective _ _
  have hιo : ∀ (i : Fin k) e (y : Γ(kerSeq M T e, (U : X.Opens))),
      secMap (kerι M T (e + 1)) (U : X.Opens)
          (secMap (kerOps hM.comm i e) (U : X.Opens) y) =
        secMap (T i.castSucc e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) := by
    intro i e y
    rw [secMap_comp, secMap_comp, kerOps_comp_kerι]
  set S : Submodule Γ(X, U) Γ(kerSeq M T (e + 1), (U : X.Opens)) :=
    Submodule.span Γ(X, U) (⋃ i, Set.range ((kerOps hM.comm i e).app U)) with hS

  have hle : LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) ≤
      S.map (secMap (kerι M T (e + 1)) (U : X.Opens)) := by
    rw [← hd' e he]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : Γ(kerSeq M T e, (U : X.Opens)), secMap (kerι M T e) (U : X.Opens) y = x :=
      kernel_ι_app_exact (T (Fin.last k) e) (U : X.Opens) x hx
    subst hy
    change secMap (T i e) (U : X.Opens) (secMap (kerι M T e) (U : X.Opens) y) ∈ _
    induction i using Fin.lastCases with
    | last =>
      rw [show secMap (T (Fin.last k) e) (U : X.Opens)
          (secMap (kerι M T e) (U : X.Opens) y) = 0 from hx]
      exact Submodule.zero_mem _
    | cast i =>
      refine ⟨secMap (kerOps hM.comm i e) (U : X.Opens) y, ?_, hιo i e y⟩
      exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, y, rfl⟩)
  rw [eq_top_iff]
  intro z _
  have hz : secMap (kerι M T (e + 1)) (U : X.Opens) z ∈
      LinearMap.ker (secMap (T (Fin.last k) (e + 1)) (U : X.Opens)) := by
    rw [LinearMap.mem_ker, secMap_comp, kerι_comp]
    simp [secMap_apply, Scheme.Modules.Hom.zero_app]
  obtain ⟨w, hw, hwz⟩ := hle hz
  rwa [← hι _ hwz]

end GlobalTheory.CompanionTheory.GE.UV
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_operators_eventually_generate : GlobalTheory.CompanionTheory.GE.GradedNoeth → ∀ {X : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d) (U : X.affineOpens), ∃ d₁ : ℕ, ∀ e, d₁ ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((GlobalTheory.CompanionTheory.GE.UV.kerOps hM.comm i e).app U)) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.UV.kerOps_gen_bounded
end

section
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem π_cokOps {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokernel.π (T (Fin.last k) e) ≫ cokOps hc i e =
      T i.castSucc (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) := by
  exact cokernel.π_desc _ _ _

theorem app_comp_apply {X : Scheme.{0}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (x : Γ(A, U)) : g.app U (f.app U x) = (f ≫ g).app U x := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

theorem app_apply_eq_of_comp_eq {X : Scheme.{0}} {A B B' C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ B') (g' : B' ⟶ C) (h : f ≫ g = f' ≫ g') (U : X.Opens) (x : Γ(A, U)) :
    g.app U (f.app U x) = g'.app U (f'.app U x) := by
  rw [app_comp_apply, app_comp_apply, h]

theorem cokOpSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    OpSeq k (cokSeq M T) (cokOps hM.comm) d where
  coherent e := by
    haveI := (hM.coherent e).1
    exact isCoherent_cokernel (T (Fin.last k) e) (hM.coherent (e + 1))
  comm := cokOps_comm hM.comm
  gen e he U := by
    haveI := (hM.coherent (e + 1)).1
    haveI := (hM.coherent (e + 1 + 1)).1
    rw [eq_top_iff]
    rintro y -
    obtain ⟨z, rfl⟩ := surjective_cokernel_π_app (T (Fin.last k) (e + 1)) U.2 y
    have hz : z ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i (e + 1)).app U)) := by
      rw [hM.gen (e + 1) (by omega) U]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hz
      induction i using Fin.lastCases with
      | last =>
        have h0 : T (Fin.last k) (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) = 0 :=
          cokernel.condition _
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h0,
          Scheme.Modules.Hom.zero_app]
        exact Submodule.zero_mem _
      | cast i =>
        refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (cokernel.π (T (Fin.last k) e)).app U x, ?_⟩)
        exact app_apply_eq_of_comp_eq (B := cokSeq M T e) (C := cokSeq M T (e + 1))
          (cokernel.π (T (Fin.last k) e)) (cokOps hM.comm i e) (T i.castSucc (e + 1))
          (cokernel.π (T (Fin.last k) (e + 1))) (π_cokOps hM.comm i e) U.1 x
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ _ ha

end GlobalTheory.CompanionTheory.GE.UV
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_sequence_operator_sequence : ∀ {X : AlgebraicGeometry.Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : GlobalTheory.CompanionTheory.GE.OpSeq (k + 1) M T d), GlobalTheory.CompanionTheory.GE.OpSeq k (GlobalTheory.CompanionTheory.GE.UV.cokSeq M T) (GlobalTheory.CompanionTheory.GE.UV.cokOps hM.comm) d := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.UV.cokOpSeq
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem serre_one {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (F : X.Modules) (hF : IsCoherent F) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  letI := algebraOfOver X A
  haveI : GlobalTheory.QCoh.IsFiniteQC F := ⟨hF.1, hF.2⟩
  exact Filter.eventually_atTop.1 (GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := X ↘ Spec (.of A)) (fun _ => rfl) F hH)

theorem kerOpSeq (hG : GradedNoeth) {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    ∃ d₁ : ℕ, OpSeq k (kerSeq M T) (kerOps hM.comm) d₁ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  choose D hD using fun U : X.affineOpens => GlobalTheory.T.kernel_operators_eventually_generate hG hM U
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => U.1.isOpen) (fun x _ => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  have hcoh : ∀ e, IsCoherent (kerSeq M T e) := fun e => by
    haveI := (hM.coherent (e + 1)).1
    exact isCoherent_kernel _ (hM.coherent e)
  refine ⟨t.sup D, ⟨hcoh, kerOps_comm hM.comm, fun e he => ?_⟩⟩
  refine GlobalTheory.T.span_sections_all_affines_of_cover (fun i => (hcoh e).1) (hcoh (e + 1)).1 _ (fun x => ?_)
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨U, hxU, hD U e ((Finset.le_sup hUt).trans he)⟩

theorem vanish_of_ker_cok {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    {M : ℕ → X.Modules} (τ : ∀ e, M e ⟶ M (e + 1)) (n : ℤ)
    (h0 : ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M 0) H n) q))
    (hK : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (kernel (τ e)) H n) q))
    (hC : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (cokernel (τ e)) H n) q)) :
    ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    intro q hq
    have hL := GlobalTheory.Twist.isLB_lbZPow hH n
    let f := τ e
    let S₁ : ShortComplex X.Modules := ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
      rw [← cancel_mono (Abelian.image.ι f)]; simp)
    have hS₁ : S₁.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι f) f (kernelIsKernel f) _ (Abelian.image.fac f))
    let S₂ : ShortComplex X.Modules := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by
      simp [Abelian.image.ι])
    have hS₂ : S₂.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f))
    have h₁ := GlobalTheory.Twist.shortExact_map hL hS₁
    have h₂ := GlobalTheory.Twist.shortExact_map hL hS₂
    have hIm := GlobalTheory.cohOn.subsingleton₃ h₁ ⊤ q (ih q hq) (hK e (q + 1) (by omega))
    exact GlobalTheory.cohOn.subsingleton₂ h₂ ⊤ q hIm (hC e q hq)

theorem coh_twistZ_of_sections {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    (F : X.Modules) [F.IsQuasicoherent] (h : ∀ U : X.affineOpens, Subsingleton Γ(F, U)) (n : ℤ) (q : ℕ) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  have hz : IsZero F := (GlobalTheory.QCoh.isZero_iff_forall_affine).2 fun U hU => h ⟨U, hU⟩
  have hz' : IsZero (GlobalTheory.twistZ F H n) := (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n)).map_isZero hz
  exact GlobalTheory.cohOn.subsingleton_of_isZero hz' ⊤ q

theorem uniformVanishing (hG : GradedNoeth) : UniformVanishing := by
  intro A _ _ X _ _ H hH k
  induction k with
  | zero =>
    intro M T d hM
    have hz : ∀ e, d < e → ∀ (n : ℤ) q, Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
      intro e he n q
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      haveI := (hM.coherent (e' + 1)).1
      refine coh_twistZ_of_sections H hH.isLB _ (fun U => ?_) n q
      have := hM.gen e' (by omega) U
      simp only [Set.iUnion_of_empty, Submodule.span_empty] at this
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]
    choose N hN using fun e => serre_one (A := A) H hH (M e) (hM.coherent e)
    obtain ⟨B, hB⟩ := Finite.exists_le (fun i : Fin (d + 1) => N i)
    refine ⟨B, fun n hn e q hq => ?_⟩
    by_cases he : e ≤ d
    · exact hN e n ((hB ⟨e, by omega⟩).trans hn) q hq
    · exact hz e (by omega) n q
  | succ k ih =>
    intro M T d hM
    obtain ⟨d₁, hK⟩ := kerOpSeq hG (A := A) hM
    obtain ⟨a, ha⟩ := ih _ _ _ hK
    obtain ⟨b, hb⟩ := ih _ _ _ (GlobalTheory.T.cokernel_sequence_operator_sequence hM)
    obtain ⟨c, hc⟩ := serre_one (A := A) H hH (M 0) (hM.coherent 0)
    refine ⟨max a (max b c), fun n hn => ?_⟩
    exact vanish_of_ker_cok H hH.isLB (T (Fin.last k)) n
      (hc n (by omega)) (fun e q hq => ha n (by omega) e q hq) (fun e q hq => hb n (by omega) e q hq)

end GlobalTheory.CompanionTheory.GE.UV
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_vanishing_of_graded_noetherian : GradedNoeth → UniformVanishing := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GE.UV.uniformVanishing
end
