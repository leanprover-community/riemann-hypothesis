import Formalism.LocalToGlobal.GlobalTheory.GL6.PowSmulLatticeLeWeightLatticeTop
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified
import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticeOfRankSlopeLength
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col NumberField Module

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {ι : Type} [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

theorem majorant_kronecker_map (B Wh : HLat K) {α β : Type} [Fintype α] [Fintype β]
    (Ψ : (α → Wh.V) →ₗ[K] B.V)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (t : Matrix β α ℤ) (v : InfinitePlace K) (F F' : β → Wh.V) :
    majAt B.b B.X v ((Ψ ∘ₗ T2.kronMap K Wh.V t) F) ((Ψ ∘ₗ T2.kronMap K Wh.V t) F') =
      ∑ b, ∑ c, (((t * t.transpose) b c : ℤ) : ℂ) * majAt Wh.b Wh.X v (F b) (F' c) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hmaj]
  simp only [T2.kronMap_apply]
  have hs := fun a : α => T2.sesq_sum_zsmul (isSesq_maj Wh.b Wh.X) v (fun b => t b a) F (fun c => t c a) F'
  simp only [hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul, Matrix.mul_apply]
  push_cast
  rfl

theorem slope_eq_of_isometric_sum (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Ψ : (α → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL α Wh.L).map (Ψ.restrictScalars (𝓞 K))) :
    B.mu = Wh.mu := by
  have e := T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (1 : Matrix α α ℤ))
    (by rw [T2.kronMap_one]; exact hΨ) (1 * (1 : Matrix α α ℤ).transpose) (by simp)
    (majorant_kronecker_map B Wh Ψ hmaj 1)
  rw [T2.kronMap_one, LinearMap.comp_id, ← hL] at e
  simpa using e

theorem induced_lattice_map_sz (B Wh : HLat K) (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ) :
    (T2.piL (T2.SzIdx G) Wh.L).map ((Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)).restrictScalars (𝓞 K)) =
      B.L ⊓ U.restrictScalars (𝓞 K) := by
  haveI : FiniteDimensional K Wh.V := Module.Finite.of_basis Wh.b
  ext x
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hL]
      refine ⟨T2.kronMap K Wh.V (T2.szVec G) F, fun a _ => ?_, rfl⟩
      rw [T2.kronMap_apply]
      exact Submodule.sum_mem _ fun c _ => zsmul_mem (hF c (Set.mem_univ c)) _
    · show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) ∈ U
      rw [hU]
      exact Submodule.mem_map_of_mem (T2.kron_szVec_mem G F)
  · rintro ⟨hx, hxU⟩
    rw [hL] at hx
    obtain ⟨F0, hF0, rfl⟩ := hx
    have hxU' : Ψ F0 ∈ U := hxU
    rw [hU] at hxU'
    obtain ⟨F1, hF1, he⟩ := hxU'
    have h01 : F1 = F0 := hΨ he
    subst h01
    rw [← T2.range_kron_szVec] at hF1
    obtain ⟨F, hF⟩ := hF1
    refine ⟨F, fun c _ => ?_, ?_⟩
    · rw [← T2.kron_szVec_pt (K := K) G F c, hF]
      exact hF0 _ (Set.mem_univ _)
    · show Ψ (T2.kronMap K Wh.V (T2.szVec G) F) = Ψ F1
      rw [hF]

theorem slope_ramified_induced (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ) (h2 : ∀ i, 1 < Fintype.card (G i)) :
    (withL B (B.L ⊓ U.restrictScalars (𝓞 K))).mu =
      B.mu - Real.log (((T2.szGram G).det : ℤ) : ℝ) / (Fintype.card (T2.SzIdx G) : ℝ) := by
  have := T2.nonempty_SzIdx G h2
  haveI : Nonempty (∀ i, G i) := ⟨1⟩
  have hinj : Function.Injective (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)) :=
    hΨ.comp (T2.kron_szVec_injective G)
  have e1 := T2.kron_mu B Wh hB hW hW0 (Ψ ∘ₗ T2.kronMap K Wh.V (T2.szVec G)) hinj
    (T2.szVec G * (T2.szVec G).transpose) (by rw [T2.szVec_mul_transpose]; exact T2.det_szGram_pos G)
    (majorant_kronecker_map B Wh Ψ hmaj (T2.szVec G))
  rw [induced_lattice_map_sz G B Wh Ψ hΨ hL U hU, T2.szVec_mul_transpose] at e1
  rw [e1, slope_eq_of_isometric_sum B Wh hB hW hW0 Ψ hΨ hmaj hL]

theorem slope_ramified_induced_prime_field (B Wh : HLat K) (hB : FrameOK B) (hW : Wh.Good) (hW0 : Wh.L ≠ ⊥)
    (Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V) (hΨ : Function.Injective Ψ)
    (hmaj : ∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a))
    (hL : B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)))
    (U : Submodule K B.V) (hU : U = (RamFun.ramFun K G Wh.V).map Ψ)
    (q : ℕ) (hq : 3 ≤ q) (hG : ∀ i, Fintype.card (G i) = q - 1) :
    (withL B (B.L ⊓ U.restrictScalars (𝓞 K))).mu =
      B.mu - (Fintype.card ι : ℝ) * Real.log ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
  rw [slope_ramified_induced G B Wh hB hW hW0 Ψ hΨ hmaj hL U hU (fun i => by rw [hG i]; omega),
    T2.log_det_szGram_div G q hq hG]

end Generic

section Slice

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)]

def t2sPsi (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V) :
    ((∀ i, G i) → W) →ₗ[K] B.V :=
  ∑ g, (ρ g).comp (W.subtype.comp (LinearMap.proj g))

theorem t2sPsi_apply (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V)
    (F : (∀ i, G i) → W) : t2sPsi B ρ W F = ∑ g, ρ g (F g : B.V) := by
  simp [t2sPsi, LinearMap.sum_apply]

def t2sNm (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (i : ι) : Module.End K B.V :=
  ∑ a : G i, ρ (Pi.mulSingle i a)

theorem norm_slice_map_sum (B : HLat K) (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V) (i : ι)
    (F : (∀ i, G i) → W) :
    t2sNm B ρ i (t2sPsi B ρ W F) =
      t2sPsi B ρ W (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) := by
  rw [t2sPsi_apply, t2sPsi_apply, t2sNm, LinearMap.sum_apply]
  simp only [map_sum, Submodule.coe_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i a))
    (fun h => (ρ h) ((F ((Pi.mulSingle i a)⁻¹ * h) : W) : B.V))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem sum_inv_mulSingle_zero_iff (i : ι) {M : Type} [AddCommGroup M] (F : (∀ i, G i) → M) :
    (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0 ↔
      (fun h => ∑ a : G i, F (Pi.mulSingle i a * h)) = 0 := by
  have e : ∀ h, ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h) = ∑ a : G i, F (Pi.mulSingle i a * h) := by
    intro h
    rw [← Equiv.sum_comp (Equiv.inv (G i))]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Pi.mulSingle_inv]
  simp only [e]

variable [IsTotallyComplex K]

theorem induced_of_slice (B : HLat K) (hB : B.Good) (hB0 : B.L ≠ ⊥)
    (ρ : (∀ i, G i) →* Module.End K B.V) (W : Submodule K B.V)
    (hbij : Function.Bijective (t2sPsi B ρ W))
    (horth : ∀ v g h (x y : W), majAt B.b B.X v (ρ g (x : B.V)) (ρ h (y : B.V)) =
      if g = h then majAt B.b B.X v (x : B.V) (y : B.V) else 0)
    (hLc : ∀ F : (∀ i, G i) → W, t2sPsi B ρ W F ∈ B.L ↔ ∀ g, (F g : B.V) ∈ B.L) :
    ∃ Wh : HLat K, Wh.Good ∧ Wh.L ≠ ⊥ ∧
      ∃ Ψ : ((∀ i, G i) → Wh.V) →ₗ[K] B.V, Function.Injective Ψ ∧
        (∀ v F F', majAt B.b B.X v (Ψ F) (Ψ F') = ∑ a, majAt Wh.b Wh.X v (F a) (F' a)) ∧
        B.L = (T2.piL (∀ i, G i) Wh.L).map (Ψ.restrictScalars (𝓞 K)) ∧
        (⨅ i, LinearMap.ker (t2sNm B ρ i)) = (RamFun.ramFun K G Wh.V).map Ψ := by
  haveI : Module.Finite K B.V := Module.Finite.of_basis B.b
  have hsub : Function.Injective W.subtype := Subtype.val_injective
  obtain ⟨hX, hm, -⟩ := pull_spec1 B (Module.finBasis K W) W.subtype hB.1 hsub
  set Ψ := t2sPsi B ρ W with hΨ

  have hL : B.L = (T2.piL (∀ i, G i) (B.L.comap (W.subtype.restrictScalars (𝓞 K)))).map
      (Ψ.restrictScalars (𝓞 K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := hbij.2 x
      exact ⟨F, fun g _ => (hLc F).1 hx g, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact (hLc F).2 fun g => hF g (Set.mem_univ g)

  let e := LinearEquiv.ofBijective Ψ hbij
  let π : B.V →ₗ[K] W := (LinearMap.proj (1 : ∀ i, G i)).comp e.symm.toLinearMap
  have hπ : ∀ w : W, π (w : B.V) = w := by
    intro w
    have h1 : Ψ (Pi.single 1 w) = (w : B.V) := by
      rw [hΨ, t2sPsi_apply, Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp
      · intro g _ hg
        simp [hg]
      · simp
    show (e.symm (w : B.V)) 1 = w
    have h2 : e.symm (w : B.V) = Pi.single 1 w := by
      rw [LinearEquiv.symm_apply_eq]
      exact h1.symm
    rw [h2]
    simp
  have hπL : ∀ x ∈ B.L, π x ∈ B.L.comap (W.subtype.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨F, rfl⟩ := hbij.2 x
    have h3 : π (Ψ F) = F 1 := by
      show (e.symm (e F)) 1 = F 1
      rw [LinearEquiv.symm_apply_apply]
    rw [h3]
    exact (hLc F).1 hx 1
  refine ⟨sub B W, ⟨hX, comap_fg W.subtype hsub hB.2.1, ?_⟩, ?_, Ψ, hbij.1, ?_, hL, ?_⟩
  ·
    rw [eq_top_iff]
    intro w _
    have hw : (w : B.V) ∈ Submodule.span K (B.L : Set B.V) := by rw [hB.2.2]; trivial
    have h4 := Submodule.mem_map_of_mem (f := π) hw
    rw [Submodule.map_span, hπ] at h4
    refine Submodule.span_mono ?_ h4
    rintro _ ⟨x, hx, rfl⟩
    exact hπL x hx
  ·
    intro h0
    apply hB0
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨F, rfl⟩ := hbij.2 x
    have hF : ∀ g, F g = 0 := by
      intro g
      have h5 : (F g : B.V) ∈ B.L := (hLc F).1 hx g
      have h6 : F g ∈ (sub B W).L := h5
      rw [h0, Submodule.mem_bot] at h6
      exact h6
    rw [t2sPsi_apply]
    simp [hF]
  ·
    intro v F F'
    rw [hΨ, t2sPsi_apply, t2sPsi_apply]
    have hs := T2.sesq_sum_zsmul (isSesq_maj B.b B.X) v (fun _ => (1 : ℤ)) (fun g => ρ g (F g : B.V))
      (fun _ => (1 : ℤ)) (fun h => ρ h (F' h : B.V))
    simp only [one_smul, Int.cast_one, one_mul] at hs
    rw [hs]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_eq_single g]
    · rw [horth, if_pos rfl, hm]
      rfl
    · intro h _ hgh
      rw [horth, if_neg (Ne.symm hgh)]
    · simp
  ·
    ext x
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map]
    constructor
    · intro hx
      obtain ⟨F, rfl⟩ := hbij.2 x
      refine ⟨F, ?_, rfl⟩
      simp only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i
      have h7 := hx i
      rw [norm_slice_map_sum] at h7
      have h8 : (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0 :=
        hbij.1 (h7.trans (map_zero _).symm)
      rw [sum_inv_mulSingle_zero_iff] at h8
      funext h
      have := congrFun h8 h
      simp only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢
      exact this
    · rintro ⟨F, hF, rfl⟩ i
      simp only [RamFun.ramFun, Submodule.mem_iInf, LinearMap.mem_ker] at hF
      have h9 := hF i
      rw [norm_slice_map_sum]
      have h10 : (fun h => ∑ a : G i, F (Pi.mulSingle i a * h)) = 0 := by
        funext h
        have := congrFun h9 h
        simp only [RamFun.nmF, LinearMap.sum_apply, Finset.sum_apply, RamFun.trl_apply, Pi.zero_apply] at this ⊢
        exact this
      rw [← sum_inv_mulSingle_zero_iff] at h10
      show t2sPsi B ρ W (fun h => ∑ a : G i, F ((Pi.mulSingle i a)⁻¹ * h)) = 0
      rw [h10, map_zero]

end Slice

section AtD

variable (D : D7) (u : D.what₂.Word)

open Classical

abbrev t2sG : (D.mem u).A.vT → Type := fun v => ((D.mem u).A.Fv v)ˣ

def InducedLattice : Prop :=
  ∃ Wh : HLat D.what₂.LL, Wh.Good ∧ Wh.L ≠ ⊥ ∧
    ∃ Ψ : ((∀ v, t2sG D u v) → Wh.V) →ₗ[D.what₂.LL] ((D.fm u).lat 0).V,
      Function.Injective Ψ ∧
      (∀ v F F', majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (Ψ F) (Ψ F') =
        ∑ a, majAt Wh.b Wh.X v (F a) (F' a)) ∧
      ((D.fm u).lat 0).L = (T2.piL (∀ v, t2sG D u v) Wh.L).map (Ψ.restrictScalars (𝓞 D.what₂.LL)) ∧
      (D.fm u).ramSub = (RamFun.ramFun D.what₂.LL (t2sG D u) Wh.V).map Ψ

theorem three_le_level_prime (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) : 3 ≤ (D.mem u).A.T := by
  have h1 := hS.1
  have hf : 0 < D.R.f := by
    show 0 < 2 * D.R.n
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    omega
  have hN : 0 < D.R.N D.R.m := D.R.N_pos _
  have : 1 ≤ D.R.f * D.R.N D.R.m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hf.ne' hN.ne')
  nlinarith

theorem slope_formula_of_induced (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (h : InducedLattice D u) : RamifiedSlopeFormula D u := by
  obtain ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩ := h
  have hB : FrameOK ((D.fm u).lat 0) := ((D.fm u).lat_good 0).1
  have hG : ∀ v, Fintype.card (t2sG D u v) = (D.mem u).A.T - 1 := fun v => by
    rw [Fintype.card_units, (D.mem u).A.card_Fv v]
  have e := slope_ramified_induced_prime_field (t2sG D u) ((D.fm u).lat 0) Wh hB hW hW0 Ψ hΨ hmaj hL (D.fm u).ramSub hU
    (D.mem u).A.T (three_le_level_prime D u hS) hG
  rw [(D.mem u).A.card_vT] at e
  exact e

end AtD

section AtDSlice

variable (D : D7) (u : D.what₂.Word)

open Classical

theorem embedding_mem_forms_level_zero (x : ((D.fm u).lat 0).V) : (D.fm u).emb 0 x ∈ (D.mem u).A.Mu0 := by
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]
  have hx := ((D.fm u).lat 0).b.sum_repr x
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem ramified_sub_eq_inf_norm_ker (ρ : (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V)
    (hρ : ∀ v a x, (D.fm u).emb 0 (ρ (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x)) :
    (D.fm u).ramSub = ⨅ v, LinearMap.ker (t2sNm ((D.fm u).lat 0) ρ v) := by
  have key : ∀ v x, (D.fm u).emb 0 (t2sNm ((D.fm u).lat 0) ρ v x) = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
    intro v x
    simp only [t2sNm, ColumnsAtT.Nm, LinearMap.sum_apply, map_sum, hρ]
  ext x
  simp only [MemberForms.ramSub, Submodule.mem_comap, ColumnsAtT.Mram, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker]
  constructor
  · rintro ⟨-, h⟩ v
    apply (D.fm u).emb_inj 0
    rw [key, h v, map_zero]
  · intro h
    exact ⟨embedding_mem_forms_level_zero D u x, fun v => by rw [← key, h v, map_zero]⟩

theorem slope_formula_of_slice (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u)
    (ρ : (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V)
    (hρ : ∀ v a x, (D.fm u).emb 0 (ρ (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x))
    (W : Submodule D.what₂.LL ((D.fm u).lat 0).V)
    (hbij : Function.Bijective (t2sPsi ((D.fm u).lat 0) ρ W))
    (horth : ∀ v g h (x y : W), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (ρ g (x : ((D.fm u).lat 0).V))
        (ρ h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0)
    (hLc : ∀ F : (∀ v, t2sG D u v) → W, t2sPsi ((D.fm u).lat 0) ρ W F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L)
    (hL0 : ((D.fm u).lat 0).L ≠ ⊥) : RamifiedSlopeFormula D u := by
  obtain ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, hU⟩ :=
    induced_of_slice ((D.fm u).lat 0) ((D.fm u).lat_good 0) hL0 ρ W hbij horth hLc
  exact slope_formula_of_induced D u hS ⟨Wh, hW, hW0, Ψ, hΨ, hmaj, hL, (ramified_sub_eq_inf_norm_ker D u ρ hρ).trans hU⟩

end AtDSlice

section Desc

variable {K V Y : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module ℂ Y] {σ : K →+* ℂ}

def t2sDesc (e : V →ₛₗ[σ] Y) (he : Function.Injective e) (R : Y →ₗ[ℂ] Y) (hR : ∀ x, ∃ y, e y = R (e x)) :
    V →ₗ[K] V where
  toFun x := (hR x).choose
  map_add' x x' := he (by
    rw [(hR (x + x')).choose_spec, map_add e (hR x).choose (hR x').choose, (hR x).choose_spec, (hR x').choose_spec,
      map_add, map_add])
  map_smul' c x := he (by
    rw [(hR (c • x)).choose_spec, RingHom.id_apply, map_smulₛₗ e c (hR x).choose, (hR x).choose_spec, map_smulₛₗ,
      map_smul])

theorem t2sDesc_spec (e : V →ₛₗ[σ] Y) (he : Function.Injective e) (R : Y →ₗ[ℂ] Y) (hR : ∀ x, ∃ y, e y = R (e x))
    (x : V) : e (t2sDesc e he R hR x) = R (e x) := (hR x).choose_spec

end Desc

section Rho

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

theorem rho_preserves_rational_forms (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) :
    ∃ y, (D.fm u).emb 0 y = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) := by
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, hy⟩ := (D.fm u).rhoT_lat v a x hx
    exact ⟨y, hy⟩
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y', hy'⟩ := hx'
    exact ⟨y + y', by rw [map_add, hy, hy', map_add, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨y, hy⟩ := hx
    exact ⟨c • y, by rw [map_smulₛₗ, hy, map_smulₛₗ, map_smul]⟩

def t2sRv (v : (D.mem u).A.vT) : ((D.mem u).A.Fv v)ˣ →* Module.End D.what₂.LL ((D.fm u).lat 0).V where
  toFun a := t2sDesc ((D.fm u).emb 0) ((D.fm u).emb_inj 0) ((D.mem u).A.rhoT v a) (rho_preserves_rational_forms v a)
  map_one' := by
    apply LinearMap.ext; intro x
    apply (D.fm u).emb_inj 0
    rw [t2sDesc_spec, map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext; intro x
    apply (D.fm u).emb_inj 0
    rw [t2sDesc_spec, map_mul, Module.End.mul_apply, Module.End.mul_apply, t2sDesc_spec, t2sDesc_spec]

theorem t2sRv_spec (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) :
    (D.fm u).emb 0 (t2sRv v a x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) :=
  t2sDesc_spec _ ((D.fm u).emb_inj 0) _ _ x

theorem embedding_mem_forms (x : ((D.fm u).lat 0).V) : (D.fm u).emb 0 x ∈ (D.fm u).Fi 0 := by
  rw [(D.fm u).Fi_zero]; exact embedding_mem_forms_level_zero D u x

theorem t2sRv_comm (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2sRv (D := D) (u := u) v x) (t2sRv v' y) := by
  intro v v' hvv a b
  apply LinearMap.ext; intro x
  apply (D.fm u).emb_inj 0
  show (D.fm u).emb 0 (t2sRv v a (t2sRv v' b x)) = (D.fm u).emb 0 (t2sRv v' b (t2sRv v a x))
  rw [t2sRv_spec, t2sRv_spec, t2sRv_spec, t2sRv_spec]
  have := diamond_comm_distinct_places Tf hE 0 (Nat.zero_le _) v' v (Ne.symm hvv) a b ((D.fm u).emb 0 x) (embedding_mem_forms x)
  rw [diamond_eq_rho, diamond_eq_rho, diamond_eq_rho, diamond_eq_rho] at this
  exact this

def t2sRho (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    (∀ v, t2sG D u v) →* Module.End D.what₂.LL ((D.fm u).lat 0).V :=
  MonoidHom.noncommPiCoprod t2sRv (t2sRv_comm Tf hE)

theorem t2sRho_single (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (x : ((D.fm u).lat 0).V) :
    (D.fm u).emb 0 (t2sRho Tf hE (Pi.mulSingle v a) x) = (D.mem u).A.rhoT v a ((D.fm u).emb 0 x) := by
  rw [t2sRho, MonoidHom.noncommPiCoprod_mulSingle, t2sRv_spec]

end Rho

section Classes

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

def t2sDv (v : (D.mem u).A.vT) : ((D.mem u).A.Fv v)ˣ →* Function.End ((D.mem u).C.cls 0) where
  toFun a := (D.fm u).dil 0 v a
  map_one' := by funext c; exact (D.fm u).dil_one 0 v c
  map_mul' a b := by funext c; exact (D.fm u).dil_mul 0 v a b c

theorem t2sDv_comm (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) :
    Pairwise fun v v' => ∀ x y, Commute (t2sDv (D := D) (u := u) v x) (t2sDv v' y) := by
  intro v v' hvv a b
  funext c
  obtain ⟨ka, hka, δa, ha⟩ := hE 0 (Nat.zero_le _) v a
  obtain ⟨kb, hkb, δb, hb⟩ := hE 0 (Nat.zero_le _) v' b
  exact dilation_commute_distinct Tf v v' hvv _ _ ka kb hka hkb δa δb ha hb c

def t2sAc (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) : (∀ v, t2sG D u v) →* Function.End ((D.mem u).C.cls 0) :=
  MonoidHom.noncommPiCoprod t2sDv (t2sDv_comm Tf hE)

theorem t2sAc_single (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls 0) : t2sAc Tf hE (Pi.mulSingle v a) c = (D.fm u).dil 0 v a c := by
  rw [t2sAc, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem group_action_mul (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g h : ∀ v, t2sG D u v) (c : (D.mem u).C.cls 0) :
    t2sAc Tf hE (g * h) c = t2sAc Tf hE g (t2sAc Tf hE h c) := by
  rw [map_mul]; rfl

theorem group_rep_transport_value (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ c : (D.mem u).C.cls 0, ∃ e : ((D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.Y 0 → ℂ),
      ∀ x, (D.fm u).emb 0 (t2sRho Tf hE g x) c = e ((D.fm u).emb 0 x (t2sAc Tf hE g c)) := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ c : (D.mem u).C.cls 0, ∃ e : ((D.mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((D.mem u).C.Y 0 → ℂ),
      ∀ x, (D.fm u).emb 0 (t2sRho Tf hE g x) c = e ((D.fm u).emb 0 x (t2sAc Tf hE g c))) ?_ ?_ ?_
  · intro a b ha hb c
    obtain ⟨ea, hea⟩ := ha c
    obtain ⟨eb, heb⟩ := hb (t2sAc Tf hE a c)
    refine ⟨eb.trans ea, fun x => ?_⟩
    rw [map_mul, Module.End.mul_apply, hea, heb, mul_comm a b, group_action_mul]
    rfl
  · intro c
    refine ⟨LinearEquiv.refl ℂ _, fun x => ?_⟩
    rw [map_one, map_one]
    rfl
  · intro v _ c
    refine ⟨(D.fm u).dilT 0 v (g v) c, fun x => ?_⟩
    rw [t2sRho_single, (D.fm u).rhoT_dil, t2sAc_single]

def t2sPc [Fact (D.mem u).A.T.Prime] : (∀ v, t2sG D u v) ≃* ((D.mem u).A.vT → (ZMod (D.mem u).A.T)ˣ) :=
  MulEquiv.piCongrRight fun v => t2xU v

theorem t2sPc_single [Fact (D.mem u).A.T.Prime] (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    t2sPc (D := D) (u := u) (Pi.mulSingle v a) = Pi.mulSingle v (t2xU v a) := by
  funext w
  simp only [t2sPc, MulEquiv.piCongrRight_apply]
  rcases eq_or_ne w v with rfl | h
  · simp
  · simp [Pi.mulSingle_eq_of_ne h]

theorem group_action_eq_unit_action [Fact (D.mem u).A.T.Prime] (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ c, t2sAc Tf hE g c = t2xAc Tf hE (t2sPc g) c := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ c, t2sAc Tf hE g c = t2xAc Tf hE (t2sPc g) c) ?_ ?_ ?_
  · intro a b ha hb c
    rw [group_action_mul, hb, ha, map_mul, map_mul]
    rfl
  · intro c
    rw [map_one, map_one, map_one]
  · intro v _ c
    rw [t2sAc_single, t2sPc_single, group_action_mulSingle_eq_dilation, MulEquiv.symm_apply_apply]

theorem group_acts_freely_classes' (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v)
    (c : (D.mem u).C.cls 0) (h : t2sAc Tf hE g c = c) : g = 1 := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h1 := group_acts_freely_classes Tf hS hE (t2sPc g) c (by rw [← group_action_eq_unit_action]; exact h)
  exact t2sPc.injective (h1.trans (map_one _).symm)

end Classes

section SliceTied

variable {D : D7} {u : D.what₂.Word}

open Classical Formalism.L2.Forms

theorem restriction_rational_form (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V)
    (S : (D.mem u).C.cls 0 → Prop) :
    ∃ y, (D.fm u).emb 0 y = fun c => if S c then (D.fm u).emb 0 x c else 0 := by
  have hr := ((Tf.val 0 (Nat.zero_le _)).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  have h0 : (D.fm u).emb 0 x ∈ (D.mem u).A.Mu0 := by rw [← (D.fm u).Fi_zero]; exact hr.1
  rw [mem_forms_level_zero_iff Tf hS] at h0
  refine ((Tf.val 0 (Nat.zero_le _)).rat _).2 ⟨?_, fun c => ?_⟩
  · rw [(D.fm u).Fi_zero, mem_forms_level_zero_iff Tf hS]
    intro c
    by_cases hc : S c
    · simp only [hc, if_true]; exact h0 c
    · simp only [hc, if_false]; exact (levelZeroValues Tf).zero_mem
  · by_cases hc : S c
    · simp only [hc, if_true]; exact hr.2 c
    · refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [hc, if_false, map_zero, Pi.zero_apply]

theorem lattice_level_zero_ne_bot (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : ((D.fm u).lat 0).L ≠ ⊥ := by
  intro h0
  have hV : ∀ x : ((D.fm u).lat 0).V, x = 0 := by
    intro x
    have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
      rw [((D.fm u).lat_good 0).2.2]; trivial
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hx
    exact (Submodule.mem_bot _).1 hx
  obtain ⟨c0, -⟩ := (Tf.cls 0 (Nat.zero_le _)).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨w, hw, hw0⟩ := level_zero_values_ne_bot Tf
  have hmem : (Pi.single c0 w : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) ∈ (D.mem u).A.Mu0 := by
    rw [mem_forms_level_zero_iff Tf hS]
    intro c
    by_cases hc : c = c0
    · subst hc; rw [Pi.single_eq_same]; exact hw
    · rw [Pi.single_eq_of_ne hc]; exact (levelZeroValues Tf).zero_mem
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2] at hmem
  have hsp : Submodule.span ℂ (Set.range fun a => (D.fm u).emb 0 (((D.fm u).lat 0).b a)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨a, rfl⟩
    show (D.fm u).emb 0 (((D.fm u).lat 0).b a) = 0
    rw [hV (((D.fm u).lat 0).b a), map_zero]
  rw [hsp, Submodule.mem_bot] at hmem
  apply hw0
  have := congrFun hmem c0
  simpa using this

variable (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)

def t2sSetoid : Setoid ((D.mem u).C.cls 0) where
  r a b := ∃ g, t2sAc Tf hE g b = a
  iseqv := by
    refine ⟨fun a => ⟨1, by rw [map_one]; rfl⟩, fun {a b} ⟨g, hg⟩ => ⟨g⁻¹, ?_⟩, fun {a b c} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨g * h, ?_⟩⟩
    · rw [← hg, ← group_action_mul, inv_mul_cancel, map_one]; rfl
    · rw [group_action_mul, hh, hg]

def t2sRep (c : (D.mem u).C.cls 0) : (D.mem u).C.cls 0 :=
  (Quotient.mk (t2sSetoid Tf hE) c).out

theorem t2sRep_spec (c : (D.mem u).C.cls 0) : ∃ g, t2sAc Tf hE g c = t2sRep Tf hE c :=
  Quotient.mk_out (s := t2sSetoid Tf hE) c

theorem t2sRep_eq {a b : (D.mem u).C.cls 0} (h : ∃ g, t2sAc Tf hE g b = a) : t2sRep Tf hE a = t2sRep Tf hE b := by
  unfold t2sRep
  rw [Quotient.sound (s := t2sSetoid Tf hE) h]

theorem t2sRep_ac (g) (c : (D.mem u).C.cls 0) : t2sRep Tf hE (t2sAc Tf hE g c) = t2sRep Tf hE c :=
  t2sRep_eq Tf hE ⟨g, rfl⟩

def t2sH (c : (D.mem u).C.cls 0) : ∀ v, t2sG D u v := (t2sRep_spec Tf hE c).choose

theorem class_rep_group_elem_spec (c : (D.mem u).C.cls 0) : t2sAc Tf hE (t2sH Tf hE c) c = t2sRep Tf hE c :=
  (t2sRep_spec Tf hE c).choose_spec

theorem group_action_injective (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) {g g' : ∀ v, t2sG D u v} {c : (D.mem u).C.cls 0}
    (h : t2sAc Tf hE g c = t2sAc Tf hE g' c) : g = g' := by
  have h1 : t2sAc Tf hE (g⁻¹ * g') c = c := by
    rw [group_action_mul, ← h, ← group_action_mul, inv_mul_cancel, map_one]; rfl
  have h2 := group_acts_freely_classes' Tf hS hE _ c h1
  rw [inv_mul_eq_one] at h2
  exact h2

theorem class_rep_group_elem_unique (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) {g : ∀ v, t2sG D u v} {c : (D.mem u).C.cls 0}
    (h : t2sAc Tf hE g c = t2sRep Tf hE c) : g = t2sH Tf hE c :=
  group_action_injective Tf hE hS (h.trans (class_rep_group_elem_spec Tf hE c).symm)

def t2sW : Submodule D.what₂.LL ((D.fm u).lat 0).V where
  carrier := {x | ∀ c, t2sRep Tf hE c ≠ c → (D.fm u).emb 0 x c = 0}
  add_mem' {x y} hx hy c hc := by rw [map_add, Pi.add_apply, hx c hc, hy c hc, add_zero]
  zero_mem' c _ := by rw [map_zero]; rfl
  smul_mem' r x hx c hc := by rw [map_smulₛₗ, Pi.smul_apply, hx c hc, smul_zero]

theorem slice_value_off_summand (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) (g : ∀ v, t2sG D u v)
    (c : (D.mem u).C.cls 0) (hg : g ≠ t2sH Tf hE c) :
    (D.fm u).emb 0 (t2sRho Tf hE g (F g : ((D.fm u).lat 0).V)) c = 0 := by
  obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g c
  rw [he]
  have hn : t2sRep Tf hE (t2sAc Tf hE g c) ≠ t2sAc Tf hE g c := by
    intro h
    rw [t2sRep_ac] at h
    exact hg (class_rep_group_elem_unique Tf hE hS h.symm)
  rw [(F g).2 _ hn, map_zero]

theorem slice_map_value_at_class (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) (c : (D.mem u).C.cls 0) :
    (D.fm u).emb 0 (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F) c =
      (D.fm u).emb 0 (t2sRho Tf hE (t2sH Tf hE c) (F (t2sH Tf hE c) : ((D.fm u).lat 0).V)) c := by
  rw [t2sPsi_apply, map_sum, Finset.sum_apply, Finset.sum_eq_single (t2sH Tf hE c)]
  · intro g _ hg
    exact slice_value_off_summand Tf hE hS F g c hg
  · intro h; exact absurd (Finset.mem_univ _) h

theorem slice_map_bijective (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) :
    Function.Bijective (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE)) := by
  constructor
  · intro F F' hFF
    have hz : ∀ F0 : (∀ v, t2sG D u v) → t2sW Tf hE,
        t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F0 = 0 → F0 = 0 := by
      intro F0 h0
      funext g
      apply Subtype.ext
      apply (D.fm u).emb_inj 0
      funext r
      show (D.fm u).emb 0 (F0 g : ((D.fm u).lat 0).V) r = (D.fm u).emb 0 0 r
      rw [map_zero]
      by_cases hr : t2sRep Tf hE r = r
      · set c := t2sAc Tf hE g⁻¹ r with hc
        have hgc : t2sAc Tf hE g c = r := by
          rw [hc, ← group_action_mul, mul_inv_cancel, map_one]; rfl
        have hrep : t2sAc Tf hE g c = t2sRep Tf hE c := by
          rw [hgc, hc, t2sRep_ac, hr]
        have hH := class_rep_group_elem_unique Tf hE hS hrep
        have h1 := slice_map_value_at_class Tf hE hS F0 c
        rw [h0, map_zero, ← hH] at h1
        obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g c
        rw [he, hgc] at h1
        have h2 := congrFun h1.symm
        exact (e.map_eq_zero_iff).1 (funext fun z => by simpa using congrFun h1.symm z)
      · exact (F0 g).2 r hr
    have := hz (F - F') (by rw [map_sub, hFF, sub_self])
    exact sub_eq_zero.1 this
  · intro x
    have hy := fun g : ∀ v, t2sG D u v => restriction_rational_form Tf hS x (fun c => t2sH Tf hE c = g)
    choose y hy using hy
    have hmem : ∀ g, t2sRho Tf hE g⁻¹ (y g) ∈ t2sW Tf hE := by
      intro g c hc
      obtain ⟨e, he⟩ := group_rep_transport_value Tf hE g⁻¹ c
      rw [he, hy g]
      have hne : t2sH Tf hE (t2sAc Tf hE g⁻¹ c) ≠ g := by
        intro h
        have h1 := class_rep_group_elem_spec Tf hE (t2sAc Tf hE g⁻¹ c)
        rw [h, ← group_action_mul, mul_inv_cancel, map_one, t2sRep_ac] at h1
        exact hc h1.symm
      simp only [hne, if_false, map_zero]
    refine ⟨fun g => ⟨_, hmem g⟩, ?_⟩
    apply (D.fm u).emb_inj 0
    funext c
    rw [slice_map_value_at_class Tf hE hS]
    show (D.fm u).emb 0 (t2sRho Tf hE (t2sH Tf hE c) (t2sRho Tf hE (t2sH Tf hE c)⁻¹ (y (t2sH Tf hE c)))) c = _
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, hy]
    simp

theorem group_rep_preserves_lattice (g : ∀ v, t2sG D u v) : ∀ x ∈ ((D.fm u).lat 0).L, t2sRho Tf hE g x ∈ ((D.fm u).lat 0).L := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ x ∈ ((D.fm u).lat 0).L, t2sRho Tf hE g x ∈ ((D.fm u).lat 0).L) ?_ ?_ ?_
  · intro a b ha hb x hx
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)
  · intro x hx
    rw [map_one]; exact hx
  · intro v _ x hx
    obtain ⟨y, hyL, hy⟩ := (D.fm u).rhoT_lat v (g v) x hx
    have : y = t2sRho Tf hE (Pi.mulSingle v (g v)) x := (D.fm u).emb_inj 0 (by rw [hy, t2sRho_single])
    rw [← this]; exact hyL

def t2sQ (c : (D.mem u).C.cls 0) (f : (D.mem u).C.Y 0 → ℂ) : Prop :=
  ∀ (w : D.what₂.places.Pl) (B : GL (Fin (D.R.N 0)) D.host.E),
    IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) B →
    ∃ P ∈ IntSpan D w ((D.fm u).lam 0),
      ∀ z, f z = fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) P
        ((Tf.val 0 (Nat.zero_le _)).eY z)

theorem local_integral_zero (c : (D.mem u).C.cls 0) : t2sQ Tf c 0 := fun w B _ => ⟨0, zero_mem _, fun z => by simp⟩

theorem mem_lattice_iff_local (x : ((D.fm u).lat 0).V) : x ∈ ((D.fm u).lat 0).L ↔ ∀ c, t2sQ Tf c ((D.fm u).emb 0 x c) := by
  rw [(Tf.val 0 (Nat.zero_le _)).lat x]
  exact ⟨fun h c w B hB => h w c B hB, fun h w c B hB => h c w B hB⟩

theorem slice_mem_lattice_iff (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (F : (∀ v, t2sG D u v) → t2sW Tf hE) :
    t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) (t2sW Tf hE) F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L := by
  have hρ : ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L ↔
      t2sRho Tf hE g (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L := by
    intro g
    refine ⟨group_rep_preserves_lattice Tf hE g _, fun h => ?_⟩
    have := group_rep_preserves_lattice Tf hE g⁻¹ _ h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  simp only [hρ, mem_lattice_iff_local Tf, slice_map_value_at_class Tf hE hS]
  constructor
  · intro h g c
    by_cases hg : g = t2sH Tf hE c
    · subst hg; exact h c
    · rw [slice_value_off_summand Tf hE hS F g c hg]; exact local_integral_zero Tf c
  · intro h c
    exact h _ c

end SliceTied

section AtDTied

variable (D : D7) (u : D.what₂.Word)

open Classical Formalism.L2.Forms

theorem slope_formula_of_compatible_slice (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hE : DiamondElementsExist Tf)
    (W : Submodule D.what₂.LL ((D.fm u).lat 0).V)
    (hbij : Function.Bijective (t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) W))
    (horth : ∀ v g h (x y : W), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
        (t2sRho Tf hE g (x : ((D.fm u).lat 0).V)) (t2sRho Tf hE h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0)
    (hLc : ∀ F : (∀ v, t2sG D u v) → W, t2sPsi ((D.fm u).lat 0) (t2sRho Tf hE) W F ∈ ((D.fm u).lat 0).L ↔
      ∀ g, (F g : ((D.fm u).lat 0).V) ∈ ((D.fm u).lat 0).L)
    (hL0 : ((D.fm u).lat 0).L ≠ ⊥) : RamifiedSlopeFormula D u :=
  slope_formula_of_slice D u hS (t2sRho Tf hE) (fun v a x => t2sRho_single Tf hE v a x) W hbij horth hLc hL0

end AtDTied

section Final

variable (D : D7) (u : D.what₂.Word)

open Classical Formalism.L2.Forms

def MetricOrthogonalClasses : Prop :=
  ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
    (∀ c, (D.fm u).emb 0 x c = 0 ∨ (D.fm u).emb 0 y c = 0) →
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y = 0

def DiamondIsometry : Prop :=
  ∀ (v : InfinitePlace D.what₂.LL) (w : (D.mem u).A.vT) (a : ((D.mem u).A.Fv w)ˣ) (x y : ((D.fm u).lat 0).V),
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a x) (t2sRv w a y) =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y

variable {D u}

theorem group_rep_majorant_isometry (hI : DiamondIsometry D u) (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (g : ∀ v, t2sG D u v) :
    ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRho Tf hE g x) (t2sRho Tf hE g y) =
        majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y := by
  rw [← Finset.univ_prod_mulSingle g]
  refine Finset.prod_induction (fun i => Pi.mulSingle i (g i))
    (fun g : ∀ v, t2sG D u v => ∀ (v : InfinitePlace D.what₂.LL) (x y : ((D.fm u).lat 0).V),
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRho Tf hE g x) (t2sRho Tf hE g y) =
        majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y) ?_ ?_ ?_
  · intro a b ha hb v x y
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  · intro v x y
    rw [map_one]; rfl
  · intro w _ v x y
    rw [t2sRho, MonoidHom.noncommPiCoprod_mulSingle]
    exact hI v w (g w) x y

theorem slice_summands_orthogonal (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hO : MetricOrthogonalClasses D u) (hI : DiamondIsometry D u) (Tf : FormsTied D u)
    (hE : DiamondElementsExist Tf) :
    ∀ v g h (x y : t2sW Tf hE), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
        (t2sRho Tf hE g (x : ((D.fm u).lat 0).V)) (t2sRho Tf hE h (y : ((D.fm u).lat 0).V)) =
      if g = h then majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x : ((D.fm u).lat 0).V) (y : ((D.fm u).lat 0).V)
      else 0 := by
  intro v g h x y
  by_cases hgh : g = h
  · subst hgh
    rw [if_pos rfl, group_rep_majorant_isometry hI Tf hE]
  · rw [if_neg hgh]
    apply hO
    intro c
    by_cases hc : g = t2sH Tf hE c
    · right
      exact slice_value_off_summand Tf hE hS (fun _ => y) h c (fun e => hgh (hc.trans e.symm))
    · left
      exact slice_value_off_summand Tf hE hS (fun _ => x) g c hc

theorem slope_formula_of_diamonds (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hE : DiamondElementsExist Tf)
    (hO : MetricOrthogonalClasses D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_compatible_slice D u hS Tf hE (t2sW Tf hE) (slice_map_bijective Tf hE hA) (slice_summands_orthogonal hA hO hI Tf hE) (slice_mem_lattice_iff Tf hE hA)
    (lattice_level_zero_ne_bot Tf hA)

end Final

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical

variable {D : D7} {u : D.what₂.Word}

theorem rational_span_map_surjective {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hP : P ∈ RatSpan D lam) :
    ∃ Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL Q = P := by
  unfold RatSpan at hP
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, -, rfl⟩ := hp
    refine ⟨MvPolynomial.C r * ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    simp [ten, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul]
    left
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map,
      show D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ from RingHom.ext_int _ _]
  | zero => exact ⟨0, map_zero _⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | neg p _ hp =>
    obtain ⟨a, ha⟩ := hp
    exact ⟨-a, by rw [map_neg, ha]⟩

theorem polynomial_rep_of_rational_form (Tf : FormsTied D u) (x : ((D.fm u).lat 0).V) :
    ∃ Pc : (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL,
      (∀ c, (D.fm u).emb 0 x c = 0 → Pc c = 0) ∧
      ∀ c z, (D.fm u).emb 0 x c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
  have hr := ((Tf.val 0 (Nat.zero_le _)).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  choose P hP hPe using hr.2
  choose Q hQ using fun c => rational_span_map_surjective _ (P c) (hP c)
  refine ⟨fun c => if (D.fm u).emb 0 x c = 0 then 0 else Q c, fun c h => by simp [h], fun c z => ?_⟩
  by_cases h : (D.fm u).emb 0 x c = 0
  · rw [h]
    simp only [h, if_true, map_zero, Pi.zero_apply]
  · simp only [h, if_false, hQ]
    exact hPe c z

theorem norm_form_zero {n : ℕ} (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp only [nfAll]
  rw [div_eq_zero_iff]
  left
  unfold REAL.fockF
  simp

theorem majAt_swap_eq_conj {V ι : Type} [AddCommGroup V] [Module D.what₂.LL V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι D.what₂.LL V)
    (X : InfinitePlace D.what₂.LL → Matrix ι ι ℂ) (v : InfinitePlace D.what₂.LL) (x y : V) :
    majAt b X v y x = starRingEnd ℂ (majAt b X v x y) := by
  unfold majAt
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.star_def, Complex.conj_conj]
  ring

theorem metric_disjoint_support_orthogonal (Tf : FormsTied D u) : MetricOrthogonalClasses D u := by
  intro v x y hxy
  set s := v.embedding with hs
  have hv : InfinitePlace.mk s = v := InfinitePlace.mk_embedding v
  obtain ⟨C, hC, -, -⟩ := (Tf.val 0 (Nat.zero_le _)).de
  letI := D.host.cmStar
  obtain ⟨o, ho⟩ := exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s)
    (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC
  obtain ⟨Px, hPx0, hPx⟩ := polynomial_rep_of_rational_form Tf x
  obtain ⟨Py, hPy0, hPy⟩ := polynomial_rep_of_rational_form Tf y
  have hay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro a c z
    rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hPy, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      map_smul, Pi.smul_apply]
  have hxay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (x + a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Px c + MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro a c z
    rw [map_add, Pi.add_apply, Pi.add_apply, hPx, hay, map_add, map_add, Pi.add_apply]
  have key : ∀ a : D.what₂.LL, (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + a • y) (x + a • y)).re =
      (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re + (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (a • y) (a • y)).re := by
    intro a
    have e1 := Tf.norm 0 (Nat.zero_le _) s (x + a • y) _ (hxay a) o ho
    have e2 := Tf.norm 0 (Nat.zero_le _) s x Px hPx o ho
    have e3 := Tf.norm 0 (Nat.zero_le _) s (a • y) _ (hay a) o ho
    rw [hv] at e1 e2 e3
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases hxy c with h | h
    · rw [hPx0 c h]
      simp only [zero_add, map_zero, norm_form_zero, Complex.zero_re, mul_zero]
    · rw [hPy0 c h]
      simp only [mul_zero, add_zero, map_zero, norm_form_zero, Complex.zero_re]
  have a1 : ∀ x x' y : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + x') y =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x' y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).1
  have a2 : ∀ x y y' : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (y + y') =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y' :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.1
  have s2 : ∀ (a : D.what₂.LL) (x y : ((D.fm u).lat 0).V), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y) =
      s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.2.2
  have hre : ∀ a : D.what₂.LL, (s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y).re = 0 := by
    intro a
    have k := key a
    rw [a1, a2, a2, majAt_swap_eq_conj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y)] at k
    rw [s2] at k
    simp only [Complex.add_re, Complex.conj_re] at k
    linarith
  obtain ⟨a0, ha0⟩ := exists_im_ne_zero v
  have h1 := hre 1
  have h2 := hre a0
  rw [map_one, one_mul] at h1
  rw [Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero] at h2
  apply Complex.ext
  · exact h1
  · rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h ha0
    · exact h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical Formalism.UG IsDedekindDomain

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fock_form_smul_smul (c : ℂ) (f : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (c • f) (c • f) = (c * starRingEnd ℂ c) * Formalism.REAL.fockF f f := by
  by_cases hc : c = 0
  · subst hc; simp [Formalism.REAL.fockF]
  · unfold Formalism.REAL.fockF
    rw [MvPolynomial.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul', RCLike.star_def]
    ring

theorem norm_form_smul_smul (lam : ι → DomWeight n) (c : ℂ) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (c • p) (c • p) = (c * starRingEnd ℂ c) * nfAll lam p p := by
  unfold nfAll
  rw [fock_form_smul_smul, mul_div_assoc]

theorem substitution_comp (o N : ι → Matrix (Fin n) (Fin n) ℂ) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP o (subP N Q) = subP (fun τ => N τ * o τ) Q := by
  have h : (subP o).comp (subP N) = subP (fun τ => N τ * o τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, subP, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      Matrix.mul_apply, Finset.mul_sum, MvPolynomial.algebraMap_eq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  show ((subP o).comp (subP N)) Q = _
  rw [h]

variable {K : Type} [Field K]

def t2iSub (M : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₐ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (M x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

theorem substitution_polynomial_map (φ : K →+* ℂ) (M : ι → Matrix (Fin n) (Fin n) K) (P : MvPolynomial (ι × Fin n × Fin n) K) :
    MvPolynomial.map φ (t2iSub M P) = subP (fun τ => (M τ).map φ) (MvPolynomial.map φ P) := by
  have : (MvPolynomial.map φ).comp (t2iSub M).toRingHom =
      (subP (fun τ => (M τ).map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [t2iSub, subP]
    · intro x
      simp [t2iSub, subP, Matrix.map_apply]
  exact congrArg (fun h : MvPolynomial (ι × Fin n × Fin n) K →+* MvPolynomial (ι × Fin n × Fin n) ℂ => h P) this

end Gen

section Transport

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem diamond_value_root_of_unity (Tf : FormsTied D u) (hC : ChiFin Tf) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ)
    (c : (D.mem u).C.cls 0) :
    ∃ (γ : GL (Fin (D.R.N 0)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (r : D.what₂.LL), (∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1) ∧
      ∀ (x : ((D.fm u).lat 0).V) z, (D.fm u).emb 0 (t2sRv v a x) c z =
        D.what₂.embLL r * (D.fm u).emb 0 x ((D.fm u).dil 0 v a c)
          ((Tf.val 0 (Nat.zero_le _)).eY.symm
            (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ ((Tf.val 0 (Nat.zero_le _)).eY z))) := by
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf 0 (Nat.zero_le _) v a
  have hcl := (Tf.val 0 (Nat.zero_le _)).dil v a k hk c δ hδ
  obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ _ _).1 hcl
  have hκ : κ.1 ∈ (Tf.cls 0 (Nat.zero_le _)).lev.U := hκK
  obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
  have hx : ((Tf.cls 0 (Nat.zero_le _)).y c * δ).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g *
        ((Tf.cls 0 (Nat.zero_le _)).y ((D.fm u).dil 0 v a c)).1 * κ.1 := by
    rw [e]
    simp only [Subgroup.coe_mul]
    rw [← hge]
  obtain ⟨n, hn, hχ⟩ := hC
  obtain ⟨hpow, r, hr⟩ := hχ 0 (Nat.zero_le _) ⟨κ.1, hκ⟩
  have hgi : g⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := (UJ _ _).inv_mem hgU
  refine ⟨g⁻¹, hgi, r, ⟨n, hn, by rw [hr]; exact hpow⟩, fun x z => ?_⟩
  obtain ⟨gA, hgA, hgAφ⟩ := forms_from_adelic_function Tf 0 (Nat.zero_le _) ((D.fm u).emb 0 x) (embedding_mem_forms x)
  have hAd := (Submodule.mem_inf.1 hgA).1
  rw [t2sRv_spec, (D.fm u).rhoT_dil, hgAφ, (Tf.val 0 (Nat.zero_le _)).dilT v a k hk c δ hδ gA hAd]
  beta_reduce
  rw [adelic_value_translate (Tf.cls 0 (Nat.zero_le _)).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hAd g hgU _ _
    ⟨κ.1, hκ⟩ hx, hr, Equiv.apply_symm_apply]

end Transport

section Reps

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def t2iM (γ : GL (Fin (D.R.N 0)) D.host.E) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  fun τ => (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map
    (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

theorem at_infinity_matrix_map (γ : GL (Fin (D.R.N 0)) D.host.E) (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    (t2iM γ τ).map s = atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  ext i j
  simp [t2iM, atInf, embS]

theorem at_infinity_matrix_embedding (γ : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    (t2iM γ τ).map D.what₂.embLL = atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ := by
  ext i j
  simp [t2iM, atInf, bwA_embT_eq]

def t2iP (γ : GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL :=
  MvPolynomial.C (r * ∏ τ, (t2iM γ τ).det ^ shiftOf (lamT u 0) τ) * t2iSub (t2iM γ) P

theorem polynomial_function_frame_translate (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    fnOf _ (shiftOf (lamT u 0)) 1 P (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ y) =
      fnOf _ (shiftOf (lamT u 0)) (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, frameTranslate, Pi.one_apply, Matrix.one_mul]

theorem polynomial_rep_translate_rho (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
    (y : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D))) :
    D.what₂.embLL r * fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL P)
        (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ hγ y) =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (t2iP (u := u) γ r P)) y := by
  rw [polynomial_function_frame_translate]
  have h1 := fnOf_mul (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
    (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) 1 (MvPolynomial.map D.what₂.embLL P)
  simp only [Pi.one_apply, Matrix.mul_one] at h1
  have h3 : (fun τ => (t2iM γ τ).map D.what₂.embLL) = atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) :=
    funext fun τ => at_infinity_matrix_embedding γ τ
  have h4 : ∀ τ, D.what₂.embLL ((t2iM γ τ).det ^ shiftOf (lamT u 0) τ) =
      (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ := by
    intro τ
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, at_infinity_matrix_embedding]
  have hmap : MvPolynomial.map D.what₂.embLL (t2iP (u := u) γ r P) =
      (D.what₂.embLL r * ∏ τ, (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
        shiftOf (lamT u 0) τ) • subP (atInf (embT D) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E))
          (MvPolynomial.map D.what₂.embLL P) := by
    rw [t2iP, (MvPolynomial.map D.what₂.embLL).map_mul, MvPolynomial.map_C, substitution_polynomial_map, h3,
      MvPolynomial.smul_eq_C_mul, D.what₂.embLL.map_mul, map_prod]
    simp only [h4]
  erw [h1]
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, Pi.smul_apply, smul_eq_mul, hmap, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

end Reps

section Norms

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem polynomial_translate_map (φ : D.what₂.LL →+* ℂ) (γ : GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) :
    MvPolynomial.map φ (t2iP (u := u) γ r P) =
      (φ r * ∏ τ, ((t2iM γ τ).map φ).det ^ shiftOf (lamT u 0) τ) •
        subP (fun τ => (t2iM γ τ).map φ) (MvPolynomial.map φ P) := by
  rw [t2iP, (MvPolynomial.map φ).map_mul, MvPolynomial.map_C, substitution_polynomial_map, MvPolynomial.smul_eq_C_mul, φ.map_mul,
    map_prod]
  simp only [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

def t2iT (s : D.what₂.LL →+* ℂ) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (c : (D.mem u).C.cls 0)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) : ℝ :=
  ((D.mem u).C.wt 0 c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (nfAll ((D.fm u).lam 0) (subP o.1 (MvPolynomial.map s P)) (subP o.1 (MvPolynomial.map s P))).re

theorem normSq_root_of_unity_eq_one (r : D.what₂.LL) (hr : ∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1) (s : D.what₂.LL →+* ℂ) :
    Complex.normSq (s r) = 1 := by
  obtain ⟨n, hn, h⟩ := hr
  have h1 : r ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have h2 : s r ^ n = 1 := by rw [← map_pow, h1, map_one]
  have h3 : ‖s r‖ = 1 := by
    have h4 := congrArg norm h2
    rw [norm_pow, norm_one] at h4
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4
  rw [Complex.normSq_eq_norm_sq, h3, one_pow]

theorem residue_eval_translate_rho (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (r : D.what₂.LL)
    (hr : ∃ n : ℕ, 0 < n ∧ D.what₂.embLL r ^ n = 1)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) (s : D.what₂.LL →+* ℂ)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (c : (D.mem u).C.cls 0) :
    t2iT s o c (t2iP (u := u) γ r P) =
      t2iT s (frameTranslate (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) γ hγ o) c P := by
  unfold t2iT
  rw [polynomial_translate_map]
  have hM : (fun τ => (t2iM γ τ).map s) = atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) :=
    funext fun τ => at_infinity_matrix_map γ s τ
  simp only [at_infinity_matrix_map]
  set μ : ℂ := s r * ∏ τ, (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
    shiftOf (lamT u 0) τ with hμ
  rw [map_smul, substitution_comp, norm_form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul]
  have hμn : Complex.normSq μ = ∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^
      (2 * shiftOf (lamT u 0) τ) := by
    rw [hμ, map_mul, normSq_root_of_unity_eq_one r hr s, one_mul, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, Complex.normSq_eq_norm_sq, zpow_mul]
    norm_cast
  have hdet : ∀ τ, ((frameTranslate (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) γ hγ o).1 τ).det =
      (atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det * (o.1 τ).det := fun τ =>
    Matrix.det_mul _ _
  simp only [hdet, norm_mul, mul_zpow, Finset.prod_mul_distrib, hμn]
  show _ = ((D.mem u).C.wt 0 c).re * ((∏ τ, ‖(atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det‖ ^
      (2 * shiftOf (lamT u 0) τ)) * ∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (nfAll ((D.fm u).lam 0) (subP (fun τ => atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * o.1 τ)
      (MvPolynomial.map s P)) (subP (fun τ => atInf (embS D s) (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * o.1 τ)
      (MvPolynomial.map s P))).re
  ring

end Norms

section Iso

variable {D : D7} {u : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def t2iRes (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((D.fm u).lat 0).V :=
  (restriction_rational_form Tf hS x (fun c' => c' = c)).choose

theorem t2iRes_spec (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    (D.fm u).emb 0 (t2iRes Tf hS x c) = fun c' => if c' = c then (D.fm u).emb 0 x c' else 0 :=
  (restriction_rational_form Tf hS x (fun c' => c' = c)).choose_spec

set_option maxHeartbeats 1000000 in

theorem polynomial_rep_residue_eval (Tf : FormsTied D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL)
    (hP : ∀ z, (D.fm u).emb 0 x c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL P)
      ((Tf.val 0 (Nat.zero_le _)).eY z))
    (s : D.what₂.LL →+* ℂ) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) (ho : o.IsON) :
    (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) (t2iRes Tf hS x c) (t2iRes Tf hS x c)).re =
      t2iT s o c P := by
  rw [Tf.norm 0 (Nat.zero_le _) s (t2iRes Tf hS x c) (fun c' => if c' = c then P else 0) ?_ o ho]
  · rw [Finset.sum_eq_single c]
    · simp only [if_pos rfl]; rfl
    · intro c' _ hc
      simp only [hc, if_false, map_zero, norm_form_zero, Complex.zero_re, mul_zero]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro c' z
    rw [t2iRes_spec]
    by_cases h : c' = c
    · subst h; simp only [if_pos rfl]; exact hP z
    · simp only [h, if_false, map_zero, Pi.zero_apply]

def t2iDil (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).C.cls 0 ≃ (D.mem u).C.cls 0 where
  toFun := (D.fm u).dil 0 v a
  invFun := (D.fm u).dil 0 v a⁻¹
  left_inv c := by rw [← (D.fm u).dil_mul, inv_mul_cancel, (D.fm u).dil_one]
  right_inv c := by rw [← (D.fm u).dil_mul, mul_inv_cancel, (D.fm u).dil_one]

set_option maxHeartbeats 1000000 in

theorem majorant_norm_diamond_invariant (Tf : FormsTied D u) (hC : ChiFin Tf) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (v : (D.mem u).A.vT)
    (a : ((D.mem u).A.Fv v)ˣ) (x : ((D.fm u).lat 0).V) (s : D.what₂.LL →+* ℂ) :
    (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) (t2sRv v a x) (t2sRv v a x)).re =
      (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X (InfinitePlace.mk s) x x).re := by
  obtain ⟨C, hC', -, -⟩ := (Tf.val 0 (Nat.zero_le _)).de
  obtain ⟨o, ho⟩ := exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s)
    (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC'
  obtain ⟨Px, -, hPx⟩ := polynomial_rep_of_rational_form Tf x
  choose γ hγ r hr hval using fun c => diamond_value_root_of_unity Tf hC v a c
  have hrep : ∀ c z, (D.fm u).emb 0 (t2sRv v a x) c z = fnOf _ (shiftOf (lamT u 0)) 1
      (MvPolynomial.map D.what₂.embLL (t2iP (u := u) (γ c) (r c) (Px ((D.fm u).dil 0 v a c))))
      ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro c z
    rw [hval c x z, hPx, Equiv.apply_symm_apply, polynomial_rep_translate_rho]
  have hwt : ∀ c, (D.mem u).C.wt 0 c = 1 := fun c => Formalism.BasicNotions.factWtZero _ _ _ (D.mem u).C hS c
  rw [Tf.norm 0 (Nat.zero_le _) s _ _ hrep o ho, Tf.norm 0 (Nat.zero_le _) s x Px hPx o ho]
  conv_rhs => rw [← Equiv.sum_comp (t2iDil v a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := residue_eval_translate_rho (u := u) (γ c) (hγ c) (r c) (hr c) (Px ((D.fm u).dil 0 v a c)) s o c
  have ho' := frame_translate_is_orthonormal (embS D s) (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (γ c) (hγ c) o ho
  have e2 := polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s _ ho'
  have e3 := polynomial_rep_residue_eval Tf hS x ((D.fm u).dil 0 v a c) (Px ((D.fm u).dil 0 v a c)) (hPx _) s o ho
  have e4 : ∀ (o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D s))) P,
      t2iT (u := u) s o' c P = t2iT s o' ((D.fm u).dil 0 v a c) P := by
    intro o' P; unfold t2iT; rw [hwt, hwt]
  change t2iT s o c _ = t2iT s o ((D.fm u).dil 0 v a c) _
  rw [e1, e4, ← e2, e3]
  rfl

theorem diamond_isometry_at_infinity (Tf : FormsTied D u) (hC : ChiFin Tf) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : DiamondIsometry D u := by
  intro v w a x y
  have hv : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
  have hF := isSesq_comp (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X) (t2sRv w a) v
  have hG := isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v
  refine sesq_ext (F := fun x y => majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a x) (t2sRv w a y))
    (G := majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v) (σ := v.embedding) (exists_im_ne_zero v) hF hG (fun z => ?_) x y
  show majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (t2sRv w a z) (t2sRv w a z) =
    majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v z z
  have h := majorant_norm_diamond_invariant Tf hC hS w a z v.embedding
  rw [hv] at h
  rw [majAt_self, majAt_self] at h ⊢
  rw [Complex.ofReal_re, Complex.ofReal_re] at h
  rw [h]

end Iso

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

theorem slope_formula_of_isometry {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) (hI : DiamondIsometry D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_diamonds hS Tf hA (diamond_elements_exist_all Tf) (metric_disjoint_support_orthogonal Tf) hI

theorem slope_formula_of_character_finite {D : D7} {u : D.what₂.Word} (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : FormsTied D u) (hC : ChiFin Tf)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : RamifiedSlopeFormula D u :=
  slope_formula_of_isometry hS Tf hA (diamond_isometry_at_infinity Tf hC hA)


end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Parts

variable (D : D7) (u : D.what₂.Word)

def BranchLatticeLengths : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)))

def SeenPlaceLatticeLengthFormula : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))

end Parts

variable {D : D7} {u : D.what₂.Word}






end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
