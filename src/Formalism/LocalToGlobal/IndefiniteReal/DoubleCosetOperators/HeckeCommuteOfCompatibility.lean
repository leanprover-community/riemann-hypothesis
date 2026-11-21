import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeVariant
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.IndefR.NX

section Op

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

def opAt (ι : H →* G) (KH : Subgroup H) (f : H → k) (φ : G → W) (g : G) : W :=
  ∑ᶠ x : H ⧸ KH, f x.out • φ (g * ι x.out)

def resAt (ι : H →* G) (φ : G → W) (g : G) : H → W := fun y => φ (g * ι y)

def RightInv (S : Set G) (φ : G → W) : Prop := ∀ g, ∀ s ∈ S, φ (g * s) = φ g






theorem opAt_eq_sum (ι : H →* G) (KH : Subgroup H) (f : H → k) (φ : G → W) (g : G) (S : Finset (H ⧸ KH))
    (hS : ∀ x : H ⧸ KH, f x.out ≠ 0 → x ∈ S) :
    opAt ι KH f φ g = ∑ x ∈ S, f x.out • φ (g * ι x.out) := by
  unfold opAt
  refine finsum_eq_sum_of_support_subset _ fun x hx => hS x fun h0 => hx ?_
  simp [h0]


end Op

section Twist

variable {H : Type} [Group H] {k : Type} [CommRing k]

def twist (χ : H →* k) (f : H → k) : H → k := fun x => χ x * f x

theorem twist_mem {KH : Subgroup H} {χ : H →* k} (hχ : ∀ κ ∈ KH, χ κ = 1) {f : H → k} (hf : f ∈ Hecke k KH) :
    twist χ f ∈ Hecke k KH := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S, fun g hg => hS g fun h0 => hg ?_⟩
  · simp only [twist, map_mul, hχ a a.2, hχ b b.2, one_mul, mul_one, hb a b g]
  · simp [twist, h0]

theorem conv_twist {KH : Subgroup H} (hK : IsCommensurated KH) (χ : H →* k) {f₁ : H → k} (hf₁ : f₁ ∈ Hecke k KH)
    (f₂ : H → k) : conv KH (twist χ f₁) (twist χ f₂) = twist χ (conv KH f₁ f₂) := by
  funext g
  unfold conv twist
  show _ = χ g * ∑ᶠ x : H ⧸ KH, f₁ x.out * f₂ (x.out⁻¹ * g)
  classical
  set S := (Formalism.UG.P.finite_supp KH hK f₁ hf₁).toFinset
  have hS : ∀ x : H ⧸ KH, f₁ x.out ≠ 0 → x ∈ S := fun x hx => by simpa [S] using hx
  rw [finsum_eq_sum_of_support_subset _ (s := S) ?_, finsum_eq_sum_of_support_subset _ (s := S) ?_, Finset.mul_sum]
  rotate_left
  · intro x hx
    exact hS x fun h0 => hx (by simp [h0])
  · intro x hx
    exact hS x fun h0 => hx (by simp [h0])
  refine Finset.sum_congr rfl fun x _ => ?_
  have : χ x.out * χ (x.out⁻¹ * g) = χ g := by rw [← map_mul, mul_inv_cancel_left]
  calc χ x.out * f₁ x.out * (χ (x.out⁻¹ * g) * f₂ (x.out⁻¹ * g))
      = (χ x.out * χ (x.out⁻¹ * g)) * (f₁ x.out * f₂ (x.out⁻¹ * g)) := by ring
    _ = χ g * (f₁ x.out * f₂ (x.out⁻¹ * g)) := by rw [this]



end Twist

section GLv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)

abbrev Kv : Subgroup (GL (Fin n) (v.adicCompletion F)) := GLint (Fin n) (Ov F v)


variable {v n} {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]


def hkN (ι : GL (Fin n) (v.adicCompletion F) →* G) (χ : GL (Fin n) (v.adicCompletion F) →* ℂ)
    (ϖ : v.adicCompletion F) (k : ℕ) (φ : G → W) : G → W :=
  opAt ι (Kv v n) (twist χ (Tj ℂ n (Ov F v) ϖ k)) φ

theorem hkN_fun_mem {χ : GL (Fin n) (v.adicCompletion F) →* ℂ} (hχ : ∀ κ ∈ Kv v n, χ κ = 1)
    {ϖ : v.adicCompletion F} (hϖ : ϖ ≠ 0) (k : ℕ) : twist χ (Tj ℂ n (Ov F v) ϖ k) ∈ Hecke ℂ (Kv v n) :=
  twist_mem hχ (Formalism.UG.Final.TjMem _ (Ov F v) ϖ ℂ n k hϖ)



end GLv

section Reps

variable {G H : Type} [Group G] [Group H] {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

def IsDCSys (KH : Subgroup H) (α : H) (R : Finset H) : Prop :=
  (∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset α (KH : Set H) KH) ∧
  ∀ x ∈ DoubleCoset.doubleCoset α (KH : Set H) KH, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ KH

theorem dosetInd_supp {KH : Subgroup H} [DecidableEq (H ⧸ KH)] {α : H} {R : Finset H} (hR : IsDCSys KH α R)
    (x : H ⧸ KH) (hx : dosetInd k KH α x.out ≠ 0) : x ∈ R.image (QuotientGroup.mk : H → H ⧸ KH) := by
  have hm : x.out ∈ DoubleCoset.doubleCoset α (KH : Set H) KH := by
    by_contra h
    exact hx (by simp [dosetInd, Set.indicator_of_notMem h])
  obtain ⟨γ, ⟨hγR, hγ⟩, -⟩ := hR.2 _ hm
  refine Finset.mem_image.mpr ⟨γ, hγR, ?_⟩
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  exact hγ

theorem opAt_dosetInd {ι : H →* G} {KH : Subgroup H} {α : H} {R : Finset H} (hR : IsDCSys KH α R) {φ : G → W}
    (hφ : RightInv (ι '' (KH : Set H)) φ) (g : G) :
    opAt ι KH (dosetInd k KH α) φ g = ∑ γ ∈ R, φ (g * ι γ) := by
  classical
  rw [opAt_eq_sum ι KH _ φ g _ (dosetInd_supp hR), Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul KH γ
    have hmem : ((γ : H ⧸ KH)).out ∈ DoubleCoset.doubleCoset α (KH : Set H) KH := by
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp (hR.1 γ hγ)
      refine DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * κ, KH.mul_mem hb κ.2, ?_⟩
      rw [hκ, e]
      group
    rw [dosetInd, Set.indicator_of_mem hmem, Pi.one_apply, one_smul, hκ, map_mul, ← mul_assoc]
    exact hφ _ _ ⟨κ, κ.2, rfl⟩
  · intro γ hγ γ' hγ' he
    have h1 : γ⁻¹ * γ' ∈ KH := QuotientGroup.eq.mp he
    obtain ⟨c, -, hc⟩ := hR.2 γ' (hR.1 γ' hγ')
    have e1 := hc γ ⟨hγ, h1⟩
    have e2 := hc γ' ⟨hγ', by simpa using KH.one_mem⟩
    rw [e1, e2]

theorem opAt_smul (ι : H →* G) (KH : Subgroup H) (c : k) (f : H → k) (φ : G → W) (g : G) (S : Finset (H ⧸ KH))
    (hS : ∀ x : H ⧸ KH, f x.out ≠ 0 → x ∈ S) :
    opAt ι KH (c • f) φ g = c • opAt ι KH f φ g := by
  rw [opAt_eq_sum ι KH (c • f) φ g S (fun x hx => hS x fun h => hx (by simp [h])), opAt_eq_sum ι KH f φ g S hS,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]


theorem isDCSys_map [DecidableEq G] {ι : H →* G} {KH : Subgroup H} {K Kc : Subgroup G}
    (hKH : ∀ a ∈ KH, ι a ∈ K) (hKc : Kc ≤ K) (hdec : ∀ κ ∈ K, ∃ a ∈ KH, ∃ c ∈ Kc, κ = ι a * c)
    (hcomm : ∀ c ∈ Kc, ∀ y, c * ι y = ι y * c) (hback : ∀ y, ι y ∈ K → y ∈ KH)
    {α : H} {R : Finset H} (hR : IsDCSys KH α R) : IsDCSys K (ι α) (R.image ι) := by
  refine ⟨?_, ?_⟩
  · intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ
    obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp (hR.1 γ hγ)
    exact DoubleCoset.mem_doubleCoset.mpr ⟨ι a, hKH a ha, ι b, hKH b hb, by rw [e, map_mul, map_mul]⟩
  · intro x hx
    obtain ⟨κ1, hκ1, κ2, hκ2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    obtain ⟨a1, ha1, c1, hc1, rfl⟩ := hdec κ1 hκ1
    obtain ⟨a2, ha2, c2, hc2, rfl⟩ := hdec κ2 hκ2
    have hy : a1 * α * a2 ∈ DoubleCoset.doubleCoset α (KH : Set H) KH :=
      DoubleCoset.mem_doubleCoset.mpr ⟨a1, ha1, a2, ha2, rfl⟩
    have ex : ι a1 * c1 * ι α * (ι a2 * c2) = ι (a1 * α * a2) * (c1 * c2) := by
      calc ι a1 * c1 * ι α * (ι a2 * c2) = ι a1 * (c1 * ι (α * a2)) * c2 := by simp only [map_mul]; group
        _ = ι a1 * (ι (α * a2) * c1) * c2 := by rw [hcomm c1 hc1]
        _ = ι (a1 * α * a2) * (c1 * c2) := by simp only [map_mul]; group
    obtain ⟨γ, ⟨hγR, hγ⟩, huniq⟩ := hR.2 _ hy
    have hc : c1 * c2 ∈ K := K.mul_mem (hKc hc1) (hKc hc2)
    refine ⟨ι γ, ⟨Finset.mem_image_of_mem _ hγR, ?_⟩, ?_⟩
    · rw [ex, ← mul_assoc, ← map_inv, ← map_mul]
      exact K.mul_mem (hKH _ hγ) hc
    · rintro δ ⟨hδ, hδx⟩
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hδ
      congr 1
      refine huniq γ' ⟨hγ', hback _ ?_⟩
      rw [ex, ← mul_assoc, ← map_inv, ← map_mul] at hδx
      simpa only [mul_inv_cancel_right] using K.mul_mem hδx (K.inv_mem hc)

theorem opAt_dosetInd_map [DecidableEq G] {ι : H →* G} (hι : Function.Injective ι) {KH : Subgroup H}
    {K Kc : Subgroup G} (hKH : ∀ a ∈ KH, ι a ∈ K) (hKc : Kc ≤ K) (hdec : ∀ κ ∈ K, ∃ a ∈ KH, ∃ c ∈ Kc, κ = ι a * c)
    (hcomm : ∀ c ∈ Kc, ∀ y, c * ι y = ι y * c) (hback : ∀ y, ι y ∈ K → y ∈ KH)
    {α : H} {R : Finset H} (hR : IsDCSys KH α R) {φ : G → W} (hφ : RightInv (K : Set G) φ) (g : G) :
    IsDCSys K (ι α) (R.image ι) ∧ opAt ι KH (dosetInd k KH α) φ g = ∑ δ ∈ R.image ι, φ (g * δ) := by
  refine ⟨isDCSys_map hKH hKc hdec hcomm hback hR, ?_⟩
  rw [opAt_dosetInd hR (fun g s ⟨a, ha, e⟩ => e ▸ hφ g _ (hKH a ha)) g, Finset.sum_image fun x _ y _ h => hι h]

end Reps

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def compV (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : GA D V) :
    GL (Fin V.rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
  Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) (Formalism.IndefR.Lev.finE V h)

structure SplitEmb (V : HSp D) (K : Set (GA D V)) where
  Sp : Set (HeightOneSpectrum (𝓞 D.host.F))
  sp : ∀ v ∈ Sp, D.host.E ⊗[D.host.F] v.adicCompletion D.host.F ≃+* v.adicCompletion D.host.F × v.adicCompletion D.host.F
  sp_sig : ∀ v (hv : v ∈ Sp) x, sp v hv (sigR D.sp.cm.sig (v.adicCompletion D.host.F) x) = swapR _ (sp v hv x)
  sp_alg : ∀ v (hv : v ∈ Sp) (a : v.adicCompletion D.host.F), sp v hv ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)
  emb : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin V.rank) (v.adicCompletion D.host.F) →* GA D V
  emb_fin : ∀ v a, emb v a ∈ GfC V
  emb_at : ∀ v (hv : v ∈ Sp) a, Formalism.UG.bc ((RingHom.fst _ _).comp (sp v hv).toRingHom) (compV V v (emb v a)) = a
  emb_off : ∀ v ∈ Sp, ∀ a, ∀ w, w ≠ v → compV V w (emb v a) = 1
  emb_K : ∀ v, ∀ a ∈ Kv v V.rank, emb v a ∈ K
  emb_comm : ∀ v v', v ≠ v' → ∀ a b, emb v a * emb v' b = emb v' b * emb v a

def SplitEmb.triv (V : HSp D) (K : Set (GA D V)) (hK : (1 : GA D V) ∈ K) : SplitEmb V K where
  Sp := ∅
  sp _ hv := absurd hv (Set.notMem_empty _)
  sp_sig _ hv := absurd hv (Set.notMem_empty _)
  sp_alg _ hv := absurd hv (Set.notMem_empty _)
  emb _ := 1
  emb_fin _ _ := (GfC V).one_mem
  emb_at _ hv := absurd hv (Set.notMem_empty _)
  emb_off _ hv := absurd hv (Set.notMem_empty _)
  emb_K _ _ _ := hK
  emb_comm _ _ _ _ _ := by simp

def hkGA {V : HSp D} {K : Set (GA D V)} (S : SplitEmb V K) (v : HeightOneSpectrum (𝓞 D.host.F))
    (f : GL (Fin V.rank) (v.adicCompletion D.host.F) → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  opAt (S.emb v) (Kv v V.rank) f φ


variable {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

def HkTie (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ (i : X.Tw) (j : ℕ) (b : Bool), ∃ (V : HSp D) (K : Set (GA D V)) (S : SplitEmb V K)
    (ev : Y.Fm i j b →+ (GA D V → ℂ)) (vP : PlE D.host → HeightOneSpectrum (𝓞 D.host.F))
    (hf : ∀ (_ : ℕ) (P : PlE D.host), GL (Fin V.rank) ((vP P).adicCompletion D.host.F) → ℂ),
    Function.Injective ev ∧ (∀ f, RightInv K (ev f)) ∧
    (∀ k P, Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := X) i k P → vP P ∈ S.Sp) ∧
    (∀ k P, Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := X) i k P → hf k P ∈ Hecke ℂ (Kv (vP P) V.rank)) ∧
    ∀ k P, Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := X) i k P → ∀ f, ev (Y.hkF i j b k P f) = hkGA S (vP P) (hf k P) (ev f)


end Concrete

section Checks

open Formalism.BasicNotions Formalism.L2.Theta

example {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ) (ϖ : v.adicCompletion F)
    (hϖ : ϖ ≠ 0) : twist (1 : GL (Fin n) (v.adicCompletion F) →* ℂ) (Tj ℂ n (Ov F v) ϖ k) ∈ Hecke ℂ (Kv v n) :=
  hkN_fun_mem (fun _ _ => rfl) hϖ k

example {G : Type} [Group G] (S : Set G) (c : ℂ) : RightInv S (fun _ : G => c) := fun _ _ _ => rfl

end Checks

end Formalism.IndefR.NX
