import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtInfinitySet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinLocSchA

open GlobalTheory.WeilM

theorem exists_open_addStab {X : Type} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ K : AddSubgroup X, IsOpen (K : Set X) ∧ ∀ z, ∀ k ∈ K, g (z + k) = g z := by
  let K : AddSubgroup X :=
    { carrier := {k | ∀ z, g (z + k) = g z}
      zero_mem' := by intro z; simp
      add_mem' := by
        intro a b ha hb z
        rw [← add_assoc, hb, ha]
      neg_mem' := by
        intro a ha z
        have := ha (z + -a)
        simpa using this.symm }
  refine ⟨K, ?_, fun z k hk => hk z⟩
  have h1 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + k) = g z := by
    apply IsCompact.eventually_forall_of_forall_eventually hg.2
    intro z _
    have a1 : IsLocallyConstant (fun p : X × X => g (p.2 + p.1)) :=
      hg.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun p : X × X => g p.2) :=
      hg.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (0, z), a2.eventually_eq (0, z)] with p hp1 hp2
    simp only [hp1, hp2, add_zero]
  have h2 : ∀ᶠ k in nhds (0 : X), ∀ z ∈ tsupport g, g (z + -k) = g z := by
    have : Filter.Tendsto (fun k : X => -k) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact this.eventually h1
  apply AddSubgroup.isOpen_of_mem_nhds K (g := 0)
  filter_upwards [h1, h2] with k hk1 hk2
  intro z
  by_cases hz : z ∈ tsupport g
  · exact hk1 z hz
  · by_cases hz' : z + k ∈ tsupport g
    · simpa using (hk2 _ hz').symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem compact_support_locally_constant_fin : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨K, hKo, hK⟩ := exists_open_addStab hg
    refine ⟨tsupport g, K, hg.2, hKo, K.zero_mem, ?_, ?_⟩
    · intro x hx
      by_contra hc
      apply hx
      simp only [pureA]
      rw [image_eq_zero_of_notMem_tsupport hc, mul_zero]
    · intro x x' h1 h2
      simp only [pureA, ← h1]
      congr 1
      have e2 : (fun i => (x' i).2) = (fun i => (x i).2) + (fun i => (x' i).2 - (x i).2) := by
        ext i; simp
      rw [e2]
      exact hK _ _ h2
  | zero =>
    refine ⟨∅, Set.univ, isCompact_empty, isOpen_univ, trivial, ?_, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro x x' _ _; rfl
  | add Φ Ψ _ _ ihΦ ihΨ =>
    obtain ⟨C₁, K₁, hC₁, hK₁, h0₁, hs₁, hi₁⟩ := ihΦ
    obtain ⟨C₂, K₂, hC₂, hK₂, h0₂, hs₂, hi₂⟩ := ihΨ
    refine ⟨C₁ ∪ C₂, K₁ ∩ K₂, hC₁.union hC₂, hK₁.inter hK₂, ⟨h0₁, h0₂⟩, ?_, ?_⟩
    · intro x hx
      by_cases h : Φ x = 0
      · right; apply hs₂ x; intro h'; apply hx; simp [h, h']
      · left; exact hs₁ x h
    · intro x x' h1 h2
      simp only [Pi.add_apply, hi₁ x x' h1 h2.1, hi₂ x x' h1 h2.2]
  | smul a Φ _ ih =>
    obtain ⟨C, K, hC, hK, h0, hs, hi⟩ := ih
    refine ⟨C, K, hC, hK, h0, ?_, ?_⟩
    · intro x hx
      apply hs x
      intro h; apply hx; simp [h]
    · intro x x' h1 h2
      simp only [Pi.smul_apply, hi x x' h1 h2]

end GlobalTheory.FinLocSchA
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_support_compact_invariance : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := by
  atlas_forward_decl GlobalTheory.FinLocSchA.compact_support_locally_constant_fin
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

noncomputable section

namespace GlobalTheory.FinCharCut

open GlobalTheory.FinTrig

theorem exists_lev_subset {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (K : Set (κ → Af F)) (hK : K ∈ nhds (0 : κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ u : κ → Af F, Lev d u → u ∈ K := by
  rw [nhds_pi, Filter.mem_pi] at hK
  obtain ⟨I, -, t, ht, hIt⟩ := hK
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

theorem fin_char_cut : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  intro F _ _ κ _ ψ hψ C K hC hK h0 y
  classical
  obtain ⟨d, -, hdK⟩ := exists_lev_subset K (hK.mem_nhds h0)
  set yf : κ → FiniteAdeleRing (𝓞 F) F := fun i => (y i).2 with hyf
  set C' := C ∩ {z | Lev d (z - yf)}ᶜ with hC'def
  have hC' : IsCompact C' := hC.inter_right (isOpen_lev d yf).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC'.elim_nhds_subcover (fun a => {z | Lev d (z - a)})
    (fun a _ => (isOpen_lev d a).mem_nhds (by simp only [Set.mem_setOf_eq, sub_self]; exact lev_zero d))
  have hsep : ∀ a ∈ C', ∃ q ∈ (Q0 : Set (κ → AF F)), ψ (vecFin (a - yf) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, Lev d u → ψ (vecFin u ⬝ᵥ q) = 1 := fun a ha => exists_sep ψ hψ d (a - yf) ha.2
  choose! q hq0 hq1 hq2 using hsep
  set c : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun a => ψ (vecFin (a - yf) ⬝ᵥ q a) with hc
  set φ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(y ⬝ᵥ q a)) • chi ψ (q a) - c a • 1) with hφ
  have hφx : ∀ a ∈ C', ∀ x, φ a x = (1 - c a)⁻¹ * (ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) - c a) := by
    intro a ha x
    have e1 : ψ (-(y ⬝ᵥ q a)) * ψ (x ⬝ᵥ q a) = ψ (vecFin ((fun i => (x i).2) - yf) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct, dot_eq_vecFin (hq0 a ha)]
      rfl
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TP ψ := fun a ha =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem ψ (hq0 a (htC a ha))))
      (Submodule.smul_mem _ _ (one_mem_TP ψ)))
  obtain ⟨s, cc, hs, hP⟩ := exists_of_mem_TP ψ (prod_mem_TP ψ t φ hφmem)
  refine ⟨s, cc, fun b hb i => fst_eq_zero (hs b hb i), ?_, fun x hxC hxK => ?_⟩
  · rw [← hP y, Finset.prod_apply]
    refine Finset.prod_eq_one fun a ha => ?_
    rw [hφx a (htC a ha)]
    have e0 : (fun i => (y i).2) - yf = 0 := sub_self _
    have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
    rw [e0, vecFin_zero, zero_dotProduct, AddChar.map_zero_eq_one, inv_mul_cancel₀ hne]
  · rw [← hP x, Finset.prod_apply]
    have hL : ¬ Lev d ((fun i => (x i).2) - yf) := by
      intro hL
      refine hxK _ (hdK _ hL) ?_
      funext i
      simp [yf]
    have hxC' : (fun i => (x i).2) ∈ C' := ⟨hxC, hL⟩
    obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC')
    rw [Finset.prod_eq_zero hat]
    rw [hφx a (htC a hat)]
    have e : (fun i => (x i).2) - yf = ((fun i => (x i).2) - a) + (a - yf) := (sub_add_sub_cancel _ _ _).symm
    rw [e, vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul, sub_self,
      mul_zero]

end GlobalTheory.FinCharCut
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_partition_of_unity_support : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := by
  atlas_forward_decl GlobalTheory.FinCharCut.fin_char_cut
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ArchPure

open Matrix

variable {F : Type} [Field F] [NumberField F]

def mk (a : Ainf F) (b : Af F) : AF F := (a, b)

@[simp] theorem mk_fst (a : Ainf F) (b : Af F) : (mk a b).1 = a := rfl

@[simp] theorem mk_snd (a : Ainf F) (b : Af F) : (mk a b).2 = b := rfl

theorem evI_fin (b : Af F) : evI F (((0 : Ainf F), b) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem snd_of_at {z : AF F} (hz : At (evI F) z) : z.2 = 0 := by
  have h := hz (((0 : Ainf F), (1 : Af F)) : AF F) (evI_fin 1)
  have h2 : (1 : Af F) * z.2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem slice {κ : Type} [Fintype κ] (c : κ → Af F) :
    ∀ Ψ ∈ schA F κ, ∃ f' : SInf F κ, ∀ s : κ → mixedEmbedding.mixedSpace F,
      Ψ (fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i)) (c i)) = f' s := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g c • f, fun s => ?_⟩
    simp [pureA, mk, mul_comm]
  | zero => exact ⟨0, fun s => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f1, h1⟩ := hx
    obtain ⟨f2, h2⟩ := hy
    exact ⟨f1 + f2, fun s => by rw [Pi.add_apply, h1, h2, SchwartzMap.add_apply]⟩
  | smul a x _ hx =>
    obtain ⟨f1, h1⟩ := hx
    exact ⟨a • f1, fun s => by rw [Pi.smul_apply, h1, SchwartzMap.smul_apply]⟩

theorem locA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := GlobalTheory.T.adelic_schwartz_support_compact_invariance

theorem locB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := GlobalTheory.T.character_partition_of_unity_support

theorem fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ ψ T hψ hkeep hcomm Φ hΦ y hy
  obtain ⟨C, K, hC, hK, hK0, hsupp, hinv⟩ := locA Φ hΦ
  obtain ⟨s, c, hs, hy1, hm⟩ := locB ψ hψ C K hC hK hK0 y
  have hu0 : evI F (mk 0 1) = 0 := evI_fin 1
  have hub : ∀ b ∈ s, (mk 0 1 : AF F) • b = b := fun b hb => funext fun i =>
    Prod.ext (show (0 : Ainf F) * (b i).1 = (b i).1 by rw [zero_mul, hs b hb i])
      (show (1 : Af F) * (b i).2 = (b i).2 from one_mul _)
  have hsch : ∀ (b : κ → AF F) (Ψ : (κ → AF F) → ℂ), schr ψ (0, b) Ψ = fun x => ψ (x ⬝ᵥ b) * Ψ x :=
    fun b Ψ => funext fun x => by simp [schr]
  have hfac : ∀ (Ψ : (κ → AF F) → ℂ) x, (∑ b ∈ s, c b • schr ψ (0, b) Ψ) x = (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x := by
    intro Ψ x
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, hsch, smul_eq_mul]
    ring
  have hzero : (∑ b ∈ s, c b • schr ψ (0, b) Φ) = 0 := by
    funext x
    rw [hfac, Pi.zero_apply]
    by_cases hx : Φ x = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left (hm x (hsupp x hx) fun k hk he => hx ?_) _
      have hk' : (fun i => (x i).2 - (y i).2) = k := funext fun i => by
        rw [congrFun he i, Pi.add_apply]
        abel
      have e1 : Φ x = Φ (fun i => mk (x i).1 (y i).2) := hinv _ _ (fun i => rfl) (by rw [← hk'] at hk; exact hk)
      rw [e1]
      have hz : At (evI F) (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) := by
        intro u' hu'
        have h1 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu'
        funext i
        exact Prod.ext (show u'.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
          (show u'.2 * (0 : Af F) = 0 from mul_zero _)
      have e2 := hy _ hz
      have e3 : y + (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) = fun i => mk (x i).1 (y i).2 := by
        funext i
        exact Prod.ext (show (y i).1 + ((x i).1 - (y i).1) = (x i).1 by abel)
          (show (y i).2 + 0 = (y i).2 from add_zero _)
      rwa [e3] at e2
  have hT : T (∑ b ∈ s, c b • schr ψ (0, b) Φ) = ∑ b ∈ s, c b • schr ψ (0, b) (T Φ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [map_smul]
    congr 1
    have := hcomm (mk 0 1) hu0 0 b Φ hΦ
    rwa [smul_zero, hub b hb] at this
  have e := congrFun hT y
  rw [hzero, map_zero, Pi.zero_apply, hfac, hy1, one_mul] at e
  exact e.symm

end GlobalTheory.ArchPure

namespace GlobalTheory.ArchPure

open Matrix

theorem arch_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT g h hg hh f φ hφ hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  set T := om' (g, h) with hTdef
  have hkeep : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), T Φ ∈ schA F _ := fun Φ hΦ => hW.pres (g, h) Φ hΦ
  have hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')),
      T (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (T Φ) := by
    intro u hu p q Φ hΦ
    set w := G.M'.co.e.symm (p, q) with hw
    have he : G.M'.co.e (u • w) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h1 : u • (mat g - 1) = 0 := hg u hu
    have h2 : u • (mat h - 1) = 0 := hh u hu
    have e1 : mat g * (u • w) = u • w := by
      have : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
        rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
      rw [h1, Matrix.zero_mul, sub_eq_zero] at this
      exact this
    have e2 : (u • w) * (mat h)ᵀ = u • w := by
      have : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have hact : actAB (cA σ) (g, h) (u • w) = u • w := by
      simp only [actAB]
      simp only [mat] at e1 e2
      rw [e1, e2]
    have h3 := hW.impl (g, h) (u • w) Φ hΦ
    simp only [Darboux.rho, he, hact] at h3
    exact h3
  have hstd' : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  have hΦ : pure f φ ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd'
  set P : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hPdef
  have hPf : ∀ x x' : Fin a' × Fin (a + a') → AF F, (∀ i, (x i).2 = (x' i).2) → P x = P x' := by
    intro x x' hx
    simp only [hPdef]
    congr 1
    funext v
    congr 1
    funext i
    show evalV F v (x i).2 = evalV F v (x' i).2
    rw [hx i]
  have hpure : ∀ (f₀ : SInf F (Fin a' × Fin (a + a'))) x, pure f₀ φ x = f₀ (fun i => evI F (x i)) * P x :=
    fun _ _ => rfl
  by_cases h0 : ∀ x, P x = 0
  · refine ⟨f, ?_⟩
    have e : pure f φ = 0 := funext fun x => by rw [hpure, h0 x, mul_zero]; rfl
    rw [e, map_zero]
  push_neg at h0
  obtain ⟨y0, hy0⟩ := h0
  obtain ⟨f', hf'⟩ := slice (fun i => (y0 i).2) (T (pure f φ)) (hkeep _ hΦ)
  refine ⟨(P y0)⁻¹ • f', ?_⟩
  funext y
  set d : Fin a' × Fin (a + a') → AF F := fun i => mk 0 ((y0 i).2 - (y i).2) with hd
  set u : AF F := mk 0 1 with hu
  have hu0 : evI F u = 0 := evI_fin 1
  have hud : u • d = d := by
    funext i
    exact Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * _ = _ from one_mul _)
  have hsh : ∀ Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ, schr B.ψ (d, 0) Φ' = fun x => Φ' (x + d) :=
    fun Φ' => funext fun x => by simp [schr]
  have htr : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), T (fun x => Ψ (x + d)) = fun x => T Ψ (x + d) := by
    intro Ψ hΨ
    have := hcomm u hu0 d 0 Ψ hΨ
    rw [hud, smul_zero, hsh, hsh] at this
    exact this
  set c : ℂ := P y / P y0 with hc
  set Θ : (Fin a' × Fin (a + a') → AF F) → ℂ := c • fun x => pure f φ (x + d) with hΘdef
  have hΘ : Θ ∈ schA F _ := by
    refine Submodule.smul_mem _ c ?_
    have := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hT.base.std (d, 0) _ hΦ
    rwa [hsh] at this
  have hvan : ∀ z, At (evI F) z → (pure f φ - Θ) (y + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := fun i => snd_of_at (fun u' hu' => congrFun (hz u' hu') i)
    have hevI : (fun i => evI F ((y + z + d) i)) = fun i => evI F ((y + z) i) := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (((y + z) i).1 + (0 : Ainf F)) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F ((y + z) i).1
      rw [add_zero]
    have hP1 : P (y + z) = P y := hPf _ _ fun i => by
      show (y i).2 + (z i).2 = (y i).2
      rw [hz2 i, add_zero]
    have hP2 : P (y + z + d) = P y0 := hPf _ _ fun i => by
      show (y i).2 + (z i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      rw [hz2 i, add_zero]
      abel
    rw [Pi.sub_apply, hΘdef, Pi.smul_apply, smul_eq_mul, hpure, hpure, hevI, hP1, hP2, hc]
    field_simp
    ring
  have h1 := fibre B.ψ T hT.base.std hkeep hcomm _ (sub_mem hΦ hΘ) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
  have h2 : T Θ y = c * T (pure f φ) (y + d) := by
    rw [hΘdef, map_smul, htr _ hΦ]
    rfl
  have hyd : y + d = fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i))) ((y0 i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [add_zero, RingEquiv.symm_apply_apply]
    · show (y i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      abel
  rw [hpure, h1, h2, hyd, hf', SchwartzMap.smul_apply, smul_eq_mul, hc]
  field_simp

end GlobalTheory.ArchPure
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_theta_local_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  atlas_forward_decl GlobalTheory.ArchPure.arch_pure
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PureStabFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (c : AF F) (g₁ g : UA σ J)
    (hg : c • (mat g - 1) = 0) (hg₁ : c • (mat g₁ - 1) = 0) : c • (mat (g₁⁻¹ * g) - 1) = 0 := by
  have hmul : mat (g₁⁻¹ * g) = mat g₁⁻¹ * mat g := rfl
  have hNM : mat g₁⁻¹ * mat g₁ = 1 := by
    change ((g₁.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * (g₁.1 : Matrix _ _ _) = 1
    exact Units.inv_mul g₁.1
  have key : mat (g₁⁻¹ * g) - 1 = mat g₁⁻¹ * (mat g - 1) - mat g₁⁻¹ * (mat g₁ - 1) := by
    rw [hmul, Matrix.mul_sub, Matrix.mul_sub, hNM, Matrix.mul_one]; abel
  rw [key, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hg, hg₁, Matrix.mul_zero, sub_zero]

open Classical in

theorem supp_of_split {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (w : Pl F) (S : Finset (Pl F))
    (g₁ g₂ : UA σ J) (hg : ∀ u : AF F, (∀ x ∈ insert w S, evFin F x u = 0) → u • (mat (g₁ * g₂) - 1) = 0)
    (hg₁ : At (evFin F w) (mat g₁ - 1)) (hg₂ : ∀ u : AF F, At (evFin F w) u → u • (mat g₂ - 1) = 0) :
    ∀ u : AF F, (∀ x ∈ S, evFin F x u = 0) → u • (mat g₂ - 1) = 0 := by
  intro u hu
  set e : AF F := GlobalTheory.UnitaryPlaceSplit.idemAt w with he
  have hew : evFin F w e = 1 := GlobalTheory.UnitaryPlaceSplit.evFin_idemAt w
  have h1 : At (evFin F w) (u * e) := fun u' hu' => by
    change u' * (u * e) = 0
    rw [← mul_assoc]
    exact GlobalTheory.UnitaryPlaceSplit.mul_idemAt_of_evFin w (by rw [map_mul, hu', zero_mul])
  have hcw : evFin F w (u * (1 - e)) = 0 := by rw [map_mul, map_sub, map_one, hew, sub_self, mul_zero]
  have h2 : (u * (1 - e)) • (mat g₂ - 1) = 0 := by
    have e2 : g₂ = g₁⁻¹ * (g₁ * g₂) := (inv_mul_cancel_left g₁ g₂).symm
    rw [e2]
    refine smul_mat_inv_mul _ _ _ (hg _ fun x hx => ?_) (hg₁ _ hcw)
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hcw
    · rw [map_mul, hu x hx, zero_mul]
  have hsplit : u = u * e + u * (1 - e) := by ring
  rw [hsplit, add_smul, hg₂ _ h1, h2, add_zero]

theorem pure_stab_fin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT S
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro g h hg hh f φ hφ hcof
    have hg1 : g = 1 := by
      have := hg 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    have hh1 : h = 1 := by
      have := hh 1 (by simp)
      rw [one_smul, sub_eq_zero] at this
      exact Subtype.ext (Units.ext this)
    subst hg1 hh1
    refine ⟨φ, hφ, fun _ _ => rfl, ?_⟩
    rw [Prod.mk_one_one, map_one]
    rfl
  | insert w S hw ih =>
    intro g h hg hh f φ hφ hcof
    obtain ⟨g₁, g₂, rfl, hg₁, hg₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ a' G.V'.J w g
    obtain ⟨h₁, h₂, rfl, hh₁, hh₂⟩ := GlobalTheory.UnitaryPlaceSplit.exists_split_at F E σ (a + a') G.W.J w h
    have hg₂S := supp_of_split w S g₁ g₂ hg hg₁ hg₂
    have hh₂S := supp_of_split w S h₁ h₂ hh hh₁ hh₂
    obtain ⟨φ₂, hφ₂, hφ₂S, hφ₂e⟩ := ih g₂ h₂ hg₂S hh₂S f φ hφ hcof
    have hcof₂ : ∀ᶠ x in Filter.cofinite, φ₂ x = G.M'.vac x := by
      filter_upwards [hcof, S.eventually_cofinite_notMem] with x hx hxS
      rw [hφ₂S x hxS, hx]
    obtain ⟨φ', hφ', hφ'w, -, hφ'e⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT w g₁ hg₁ h₁ hh₁ f φ₂ hφ₂ hcof₂
    refine ⟨φ', hφ', fun x hx => ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at hx
      rw [hφ'w x hx.1, hφ₂S x hx.2]
    · have hpr : ((g₁ * g₂, h₁ * h₂) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) := rfl
      rw [hpr, map_mul, Module.End.mul_apply, hφ₂e, hφ'e]

end GlobalTheory.PureStabFin
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_finite_set : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  atlas_forward_decl GlobalTheory.PureStabFin.pure_stab_fin
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  first | exact @GlobalTheory.AdelMatLat.almost_all_stable | exact GlobalTheory.AdelMatLat.almost_all_stable | (intros; apply GlobalTheory.AdelMatLat.almost_all_stable <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), Y.L.IsLattice E → ∀ N : Matrix (Fin d) (Fin d) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  first | exact @GlobalTheory.AdelMatLatRight.almost_all_stable_right | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right | (intros; apply GlobalTheory.AdelMatLatRight.almost_all_stable_right <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def idemInf : AF F := LinearMap.inl F (Ainf F) (Af F) 1

def idemSet (S : Finset (Pl F)) : AF F := ∑ w ∈ S, idemAt w

theorem evI_eq (a : AF F) : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F a) := rfl

theorem evFin_idemInf (w : Pl F) : evFin F w (idemInf F) = 0 := by
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (0 : Af F) = 0
  exact map_zero _

theorem fstA_idemInf : fstA F (idemInf F) = 1 := rfl

theorem fstA_idemAt (w : Pl F) : fstA F (idemAt w) = 0 := rfl

theorem fstA_idemSet (S : Finset (Pl F)) : fstA F (idemSet S) = 0 := by
  unfold idemSet
  rw [map_sum]
  exact Finset.sum_eq_zero fun w _ => fstA_idemAt w

theorem evFin_idemAt_ne {w w' : Pl F} (h : w' ≠ w) : evFin F w' (idemAt w) = 0 := by
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w' (singleFin w 1) = 0
  exact evalV_singleFin_ne h 1

theorem idemAt_mul_ne {w w' : Pl F} (h : w' ≠ w) : idemAt w * idemAt w' = 0 :=
  mul_idemAt_of_evFin w' (evFin_idemAt_ne h)

theorem evFin_idemSet_mem {S : Finset (Pl F)} {w : Pl F} (hw : w ∈ S) : evFin F w (idemSet S) = 1 := by
  classical
  unfold idemSet
  rw [map_sum, Finset.sum_eq_single w (fun w' _ hne => evFin_idemAt_ne (Ne.symm hne)) (fun h => absurd hw h),
    evFin_idemAt]

theorem evFin_idemSet_not_mem {S : Finset (Pl F)} {w : Pl F} (hw : w ∉ S) : evFin F w (idemSet S) = 0 := by
  unfold idemSet
  rw [map_sum]
  exact Finset.sum_eq_zero fun w' hw' => evFin_idemAt_ne (by rintro rfl; exact hw hw')

theorem idemSet_mul_self (S : Finset (Pl F)) : idemSet S * idemSet S = idemSet S := by
  classical
  unfold idemSet
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single w (fun w' _ hne => idemAt_mul_ne hne) (fun h => absurd hw h),
    idemAt_mul_self]

theorem mul_idemSet_of {S : Finset (Pl F)} {u : AF F} (hu : ∀ w ∈ S, evFin F w u = 0) : u * idemSet S = 0 := by
  unfold idemSet
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun w hw => mul_idemAt_of_evFin w (hu w hw)

theorem idemInf_mul_idemSet (S : Finset (Pl F)) : idemInf F * idemSet S = 0 :=
  mul_idemSet_of fun w _ => evFin_idemInf w

theorem idemInf_mul_self : idemInf F * idemInf F = idemInf F :=
  Prod.ext (show (1 : Ainf F) * 1 = 1 from one_mul 1) (show (0 : Af F) * 0 = 0 from mul_zero 0)

theorem mul_idemInf_of_evI {u : AF F} (hu : evI F u = 0) : u * idemInf F = 0 := by
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ (show u.2 * (0 : Af F) = 0 from mul_zero _)
  change fstA F u * 1 = 0
  rw [h1, zero_mul]

end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mixM {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  e • G + (1 - e) • 1

theorem mixM_one_left {n : ℕ} (G : Matrix (Fin n) (Fin n) (AE F E)) : mixM 1 G = G := by
  simp [mixM]

theorem mixM_one_right {n : ℕ} (e : AF F) : mixM e (1 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [mixM, ← add_smul, add_sub_cancel, one_smul]

theorem mixM_sub_one {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : mixM e G - 1 = e • (G - 1) := by
  rw [mixM, smul_sub, sub_smul, one_smul]
  abel

theorem mixM_mul_same {n : ℕ} {e : AF F} (he : e * e = e) (G G' : Matrix (Fin n) (Fin n) (AE F E)) :
    mixM e G * mixM e G' = mixM e (G * G') := by
  rw [mixM, mixM, mixM, mix_mul he, mul_one]

theorem mixM_mul_orth {n : ℕ} {e f : AF F} (hef : e * f = 0) (G : Matrix (Fin n) (Fin n) (AE F E)) :
    mixM e G * mixM f G = mixM (e + f) G := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by rw [sub_mul, one_mul, mul_sub, mul_one, hef]; ring
  simp only [mixM, Matrix.add_mul, Matrix.mul_add, smul_mul_smul_comm, h1, h2, h3, hef, zero_smul, zero_add, mul_one,
    one_mul, add_smul]
  abel

theorem mixM_mul_of_smul {n d : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E))
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : e • γ = 0) : mixM (1 - e) G * γ = G * γ := by
  have h1 : e • (G * γ) = 0 := by rw [← Matrix.mul_smul, hγ, Matrix.mul_zero]
  rw [mixM, sub_sub_cancel, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hγ, add_zero, sub_smul, one_smul, h1,
    sub_zero]

theorem mul_mixM_of_smul {n d : ℕ} (e : AF F) (H : Matrix (Fin d) (Fin d) (AE F E))
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : e • γ = 0) : γ * (mixM (1 - e) H)ᵀ = γ * Hᵀ := by
  have h1 : e • (γ * Hᵀ) = 0 := by rw [← Matrix.smul_mul, hγ, Matrix.zero_mul]
  rw [mixM, sub_sub_cancel, transpose_add, transpose_smul, transpose_smul, transpose_one, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, hγ, add_zero, sub_smul, one_smul, h1, sub_zero]

variable {σ : E →ₐ[F] E}

theorem mixM_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AF F} (he : e * e = e) (g : UA σ J) :
    (mixM e (mat g))ᵀ * incM F J * (mixM e (mat g)).map (cA σ) = incM F J := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  have hT : (mixM e (mat g))ᵀ = e • (mat g)ᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mixM, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have hc : (mixM e (mat g)).map (cA σ) = e • (mat g).map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← AlgHom.mapMatrix_apply, mixM, map_add, map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
  rw [hT, hc, split (incM F J), mix_mul he, mix_mul he, hg, one_mul, mul_one]

def mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨mixM e (mat g), mixM e (mat g⁻¹),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.mul_inv g.1)).trans (mixM_one_right e),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.inv_mul g.1)).trans (mixM_one_right e)⟩,
    mixM_mem he g⟩

theorem mat_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g) = mixM e (mat g) := rfl

theorem mat_inv_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g)⁻¹ = mixM e (mat g⁻¹) := rfl

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) : mat (x * y) = mat x * mat y := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : UA σ J) : mat x⁻¹ * mat x = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_injective {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x y : UA σ J} (h : mat x = mat y) : x = y :=
  Subtype.ext (Units.ext h)

end GlobalTheory.UnitaryTriSplit

namespace GlobalTheory.UnitaryTriSplit
theorem finite_bad {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (M : Matrix (Fin n) (Fin n) (AE F E)) (N : Matrix (Fin d) (Fin d) (AE F E)) :
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, M * γ * Matrix.transpose N ∈ latAtV X Y w} := by
  refine (((GlobalTheory.T.lattice_stable_almost_all_places_left) F E n d X Y hX M).union ((GlobalTheory.T.lattice_stable_almost_all_places_right) F E n d X Y hY N)).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hw fun γ hγ => hc.2 _ (hc.1 γ hγ)
end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

theorem factor_away : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl F)) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh φ hφ
  classical
  have hX := hT.geo.hV'.lat
  have hY := hT.geo.hW.lat
  have hfin := ((Filter.eventually_cofinite.1 hφ).union (finite_bad G.V' G.W hX hY (mat g) (mat h))).union
    (finite_bad G.V' G.W hX hY (mat g⁻¹) (mat h⁻¹))
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Pl F), S = hfin.toFinset.erase v := ⟨_, rfl⟩
  have hout : ∀ w, w ≠ v → w ∉ S → w ∉ hfin.toFinset := fun w hwv hwS hm =>
    hwS (hSdef ▸ Finset.mem_erase.2 ⟨hwv, hm⟩)
  obtain ⟨e₁, e₂, h11, h22, h12, hI1, hS2, hfst1, hfst2, hevS, hevN⟩ : ∃ e₁ e₂ : AF F, e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧
      e₁ * e₂ = 0 ∧ (∀ u, evI F u = 0 → u * e₁ = 0) ∧ (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u * e₂ = 0) ∧
      fstA F e₁ = 1 ∧ fstA F e₂ = 0 ∧ (∀ w ∈ S, evFin F w (e₁ + e₂) = 1) ∧ (∀ w ∉ S, evFin F w (e₁ + e₂) = 0) :=
    ⟨idemInf F, idemSet S, idemInf_mul_self, idemSet_mul_self S, idemInf_mul_idemSet S, fun u hu => mul_idemInf_of_evI hu,
      fun u hu => mul_idemSet_of hu, fstA_idemInf, fstA_idemSet S,
      fun w hw => by rw [map_add, evFin_idemInf, evFin_idemSet_mem hw, zero_add],
      fun w hw => by rw [map_add, evFin_idemInf, evFin_idemSet_not_mem hw, zero_add]⟩
  obtain ⟨e, he⟩ : ∃ e, e₁ + e₂ = e := ⟨_, rfl⟩
  have hee : e * e = e := by
    rw [← he, add_mul, mul_add, mul_add, h11, h22, h12, mul_comm e₂ e₁, h12, zero_add, add_zero]
  have h33 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have he3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hevI : evI F (1 - e) = 0 := by
    rw [evI_eq, map_sub, map_one, ← he, map_add, hfst1, hfst2, add_zero, sub_self, map_zero]
  rw [he] at hevS hevN
  have hevS' : ∀ w ∈ S, evFin F w (1 - e) = 0 := fun w hw => by rw [map_sub, map_one, hevS w hw, sub_self]
  refine ⟨S, mixU e₁ h11 g, mixU e₂ h22 g, mixU (1 - e) h33 g, mixU e₁ h11 h, mixU e₂ h22 h, mixU (1 - e) h33 h,
    by rw [hSdef]; exact Finset.notMem_erase v _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine mat_injective ?_
    rw [mat_mul, mat_mul, mat_mixU, mat_mixU, mat_mixU, mixM_mul_orth h12, he, mixM_mul_orth he3, add_sub_cancel,
      mixM_one_left]
  · refine mat_injective ?_
    rw [mat_mul, mat_mul, mat_mixU, mat_mixU, mat_mixU, mixM_mul_orth h12, he, mixM_mul_orth he3, add_sub_cancel,
      mixM_one_left]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hI1 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hI1 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hS2 u hu, zero_smul]
  · intro u hu
    rw [mat_mixU, mixM_sub_one, smul_smul, hS2 u hu, zero_smul]
  · intro u hu
    have h0 : (1 - e) • u = 0 := hu (1 - e) hevI
    rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · intro u hu
    have h0 : (1 - e) • u = 0 := hu (1 - e) hevI
    rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · rintro w (rfl | hw) u hu
    · rw [mat_mixU, mixM_sub_one, smul_smul]
      refine hg _ fun u' hu' => ?_
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u' u, hu u' hu', zero_mul]
    · have h0 : (1 - e) • u = 0 := hu (1 - e) (hevS' w hw)
      rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · rintro w (rfl | hw) u hu
    · rw [mat_mixU, mixM_sub_one, smul_smul]
      refine hh _ fun u' hu' => ?_
      rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u' u, hu u' hu', zero_mul]
    · have h0 : (1 - e) • u = 0 := hu (1 - e) (hevS' w hw)
      rw [mat_mixU, mixM_sub_one, smul_smul, mul_comm, ← smul_eq_mul, h0, zero_smul]
  · intro w hwv hwS γ
    have hw' := hout w hwv hwS
    rw [Set.Finite.mem_toFinset] at hw'
    have good1 : ∀ γ ∈ latAtV G.V' G.W w, mat g * γ * (mat h)ᵀ ∈ latAtV G.V' G.W w := by
      by_contra hc; exact hw' (Or.inl (Or.inr hc))
    have good2 : ∀ γ ∈ latAtV G.V' G.W w, mat g⁻¹ * γ * (mat h⁻¹)ᵀ ∈ latAtV G.V' G.W w := by
      by_contra hc; exact hw' (Or.inr hc)
    have hsm : ∀ γ ∈ latAtV G.V' G.W w, e • γ = 0 := fun γ hγ =>
      (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1 γ hγ e (hevN w hwS)
    constructor
    · intro hδ
      have hδe := hsm _ hδ
      have key : γ = mat (mixU (1 - e) h33 g)⁻¹ * (mat (mixU (1 - e) h33 g) * γ * (mat (mixU (1 - e) h33 h))ᵀ) *
          (mat (mixU (1 - e) h33 h)⁻¹)ᵀ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
          ← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one, Matrix.mul_one]
      rw [key, mat_inv_mixU, mat_inv_mixU, mixM_mul_of_smul e _ hδe,
        mul_mixM_of_smul e _ (by rw [← Matrix.mul_smul, hδe, Matrix.mul_zero])]
      exact good2 _ hδ
    · intro hγ
      rw [mat_mixU, mat_mixU, mixM_mul_of_smul e _ (hsm γ hγ),
        mul_mixM_of_smul e _ (by rw [← Matrix.mul_smul, hsm γ hγ, Matrix.mul_zero])]
      exact good1 γ hγ
  · intro w hwv hwS
    have hw' := hout w hwv hwS
    rw [Set.Finite.mem_toFinset] at hw'
    by_contra hc
    exact hw' (Or.inl (Or.inl hc))

end GlobalTheory.UnitaryTriSplit
end
end
end
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_local_factor_finite_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ), (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (S : Finset (Pl F)) (g₁ g₂ g₃ : UA σ G.V'.J) (h₁ h₂ h₃ : UA σ G.W.J), v ∉ S ∧
      g = g₁ * g₂ * g₃ ∧ h = h₁ * h₂ * h₃ ∧ At (evI F) (mat g₁ - 1) ∧ At (evI F) (mat h₁ - 1) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g₂ - 1) = 0) ∧
      (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h₂ - 1) = 0) ∧
      (∀ u : AF F, At (evI F) u → u • (mat g₃ - 1) = 0) ∧ (∀ u : AF F, At (evI F) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat g₃ - 1) = 0) ∧
      (∀ w, (w = v ∨ w ∈ S) → ∀ u : AF F, At (evFin F w) u → u • (mat h₃ - 1) = 0) ∧
      (∀ w, w ≠ v → w ∉ S → ∀ γ, (mat g₃ * γ * Matrix.transpose (mat h₃) ∈ latAtV G.V' G.W w ↔ γ ∈ latAtV G.V' G.W w)) ∧
      (∀ w, w ≠ v → w ∉ S → φ w = G.M'.vac w) := by
  atlas_forward_decl GlobalTheory.UnitaryTriSplit.factor_away
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.PureAway

theorem pure_away : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT v g h hg hh f φ hφ hφv
  obtain ⟨S, g₁, g₂, g₃, h₁, h₂, h₃, hvS, rfl, rfl, a1, a2, b1, b2, c1, c2, c3, c4, c5, c6⟩ :=
    GlobalTheory.T.theta_local_factor_finite_place F E σ B a a' G X om om' hT v g h hg hh φ hφv
  obtain ⟨c, hc⟩ := GlobalTheory.T.theta_trivial_at_infinity_set P F E σ B a a' G X om om' hT (insert v S) g₃ h₃ c1 c2
    (fun w hw => c3 w (Finset.mem_insert.mp hw)) (fun w hw => c4 w (Finset.mem_insert.mp hw))
    (fun w hw => c5 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e))) f φ hφ
    (fun w hw => c6 w (fun e => hw (e ▸ Finset.mem_insert_self _ _)) (fun e => hw (Finset.mem_insert_of_mem e)))
  obtain ⟨φ₁, hφ₁, hφ₁e, he₁⟩ := GlobalTheory.T.theta_trivial_at_finite_set P F E σ B a a' G X om om' hT S g₂ h₂ b1 b2 f φ hφ hφv
  have hφ₁v : ∀ᶠ w in Filter.cofinite, φ₁ w = G.M'.vac w := by
    filter_upwards [hφv, S.finite_toSet.compl_mem_cofinite] with w hw hwS
    rw [hφ₁e w hwS, hw]
  obtain ⟨f₂, he₂⟩ := GlobalTheory.T.archimedean_theta_local_action P F E σ B a a' G X om om' hT g₁ h₁ a1 a2 f φ₁ hφ₁ hφ₁v
  refine ⟨c • f₂, φ₁, hφ₁, hφ₁v, hφ₁e v hvS, ?_⟩
  have hmul : ((g₁ * g₂ * g₃, h₁ * h₂ * h₃) : UA σ G.V'.J × UA σ G.W.J) = (g₁, h₁) * (g₂, h₂) * (g₃, h₃) := rfl
  rw [hmul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul, he₁, map_smul, he₂]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.PureAway
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_place_product : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (g : UA σ G.V'.J) (h : UA σ G.W.J), (∀ u : AF F, At (evFin F v) u → u • (mat g - 1) = 0) →
    (∀ u : AF F, At (evFin F v) u → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ (f₂ : SInf F (Fin a' × Fin (a + a'))) (φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ᶠ w in Filter.cofinite, φ₂ w = G.M'.vac w) ∧ φ₂ v = φ v ∧
      om' (g, h) (pure f φ) = pure f₂ φ₂ := by
  atlas_forward_decl GlobalTheory.PureAway.pure_away
end
