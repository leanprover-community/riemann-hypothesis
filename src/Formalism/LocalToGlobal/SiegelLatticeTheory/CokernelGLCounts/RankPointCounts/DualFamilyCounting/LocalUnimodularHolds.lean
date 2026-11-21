import Formalism.SharpRestriction.CuspSpanNormBounds.LocSplitType
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTransfer

section
noncomputable section

open Module

namespace Formalism.L2.SG.Pf.G4

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

def NondegOn (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : Prop :=
  ∀ ξ ∈ W, ξ ≠ 0 → ∃ w ∈ W, h w ξ ≠ 0

theorem exists_primitive' (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ w : V} (hξ : ξ ∈ W)
    (hw : w ∈ W) (hn : h w ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by
  obtain ⟨t, ht0, htM⟩ := hM.span w hw
  have hsp := hM.span ξ hξ
  let A : AddSubgroup K :=
    { carrier := {c | c • ξ ∈ M}
      add_mem' := fun {a b} ha hb => by
        show (a + b) • ξ ∈ M
        rw [add_smul]
        exact M.add_mem ha hb
      zero_mem' := by
        show (0 : K) • ξ ∈ M
        rw [zero_smul]
        exact M.zero_mem
      neg_mem' := fun {a} ha => by
        show (-a) • ξ ∈ M
        rw [neg_smul]
        exact M.neg_mem ha }
  have hA : ∀ c, c ∈ A ↔ c • ξ ∈ M := fun c => Iff.rfl
  obtain ⟨α, hαA, hα0, hα⟩ := hS.principal A
    (fun s hs a ha => by
      rw [hA] at ha ⊢
      rw [mul_smul]
      exact hM.smul_mem s hs _ ha)
    (by
      obtain ⟨t', ht'0, ht'M⟩ := hsp
      exact ⟨t', (hA t').2 ht'M, ht'0⟩)
    ⟨star t * h w ξ, mul_ne_zero (star_ne_zero.2 ht0) hn, fun a ha => by
      rw [hA] at ha
      have hi := hM.int _ htM _ ha
      have e : h (t • w) (a • ξ) = star t * h w ξ * a := by
        rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
        ring
      rw [← e]
      exact hi⟩
  exact ⟨α, hα0, (hA α).1 hαA, fun c hc => hα c ((hA c).2 hc)⟩

theorem exists_primitive_norm' (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W)
    {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by
  have hu0 : u ≠ 0 := hu.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hu0
    rw [← hξu]
    simp
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM hξ hξ (by rw [hξu]; exact hu0)
  have hyy : h (l • ξ) (l • ξ) = star l * l * u := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hξu]
    ring
  have hN : star l * l ∈ S := by
    have hi := hM.int _ hlM _ hlM
    rw [hyy] at hi
    have e := S.mul_mem hi hu.2.2
    rwa [mul_assoc, mul_inv_cancel₀ hu0, mul_one] at e
  obtain ⟨b, hb1, hbS⟩ := Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem hS hN
  refine ⟨l • ξ, hlM, smul_ne_zero hl0 hξ0, ⟨l, rfl⟩, fun c hc => ?_, l * b, hbS, ?_⟩
  · have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  · rw [hyy, star_mul]
    linear_combination (-(star l * l * u)) * hb1

theorem IsSD.exists_norm' (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K}
    (hu : IsUnitIn S u) (hξu : h ξ ξ = u) : ∃ X ∈ M, h X X = u := by
  obtain ⟨y, hy, -, -, hprim, a, ha, hyy⟩ := exists_primitive_norm' hS hM.toIsLatIn hξ hu hξu
  obtain ⟨w, hw, hn⟩ := hM.exists_not_dv hπ hy hprim
  have huf : star u = u := by
    have e : starRingEnd K (h ξ ξ) = h ξ ξ := by
      first
        | exact hs ξ ξ
        | exact hs.eq ξ ξ
    rw [hξu, starRingEnd_apply] at e
    exact e
  exact exists_norm_of_not_dv hS hπ hs hM.smul_mem hM.int hy hw ha hu huf hyy hn

theorem IsSD.exists_unit_norm' (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hnd : NondegOn h W) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by
  obtain ⟨w, hw, hn⟩ := hnd ξ hξ hξ0
  obtain ⟨l, hl0, hlM, hprim⟩ := exists_primitive' hS hM.toIsLatIn hξ hw hn
  have hprim' : ∀ c : K, c • (l • ξ) ∈ M → c ∈ S := by
    intro c hc
    have e := hprim (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at e
  obtain ⟨w', hw', hn'⟩ := hM.exists_not_dv hπ hlM hprim'
  exact exists_unit_norm hS hπ hs hM.smul_mem hM.int hlM hw' hn'

theorem nondegOn_cut (hnd : NondegOn h W) {x : V} (hx : x ∈ W) (hxx : h x x ≠ 0) :
    NondegOn h (cutW h W x) := by
  intro ξ hξ hξ0
  rw [mem_cutW] at hξ
  obtain ⟨w, hw, hwξ⟩ := hnd ξ hξ.1 hξ0
  refine ⟨w - (h x w * (h x x)⁻¹) • x, ?_, ?_⟩
  · rw [mem_cutW]
    refine ⟨W.sub_mem hw (W.smul_mem _ hx), ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
  · rw [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, hξ.2, smul_zero, sub_zero]
    exact hwξ

end Formalism.L2.SG.Pf.G4
end
end

section
noncomputable section

open Module

namespace Formalism.L2.SG.Pf.G4

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem exists_isom_move' (hs : h.IsSymm) {x y : V} (hxy : h x x = h y y)
    (hb : h x x - h y x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  obtain ⟨z, hz⟩ : ∃ z, z = x - y := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = h x x - h y x := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := hbd ▸ hb
  have hsb0 : star b ≠ 0 := star_ne_zero.2 hb0
  have hzx : h z x = b := by
    rw [hz, hbd, map_sub, LinearMap.sub_apply]
  have hzv : ∀ v, h z v = h x v - h y v := fun v => by
    rw [hz, map_sub, LinearMap.sub_apply]
  have hzz : h z z = b + star b := by
    have h1 : star b = h x x - h x y := by
      rw [hbd, star_sub, hsym, hsym]
    rw [h1, hbd, hzv, hz, map_sub, map_sub, hxy]
    ring
  let τl : V →ₗ[K] V := LinearMap.id - (b⁻¹ • h z).smulRight z
  let σl : V →ₗ[K] V := LinearMap.id - ((star b)⁻¹ • h z).smulRight z
  have hτ : ∀ v, τl v = v - (b⁻¹ * h z v) • z := fun v => rfl
  have hσ : ∀ v, σl v = v - ((star b)⁻¹ * h z v) • z := fun v => rfl
  have key : ∀ c d : K, c + d = c * d * h z z → ∀ v : V,
      (v - (c * h z v) • z) - (d * h z (v - (c * h z v) • z)) • z = v := by
    intro c d hcd v
    rw [map_sub, map_smul, smul_eq_mul, sub_sub, ← add_smul]
    have h0 : c * h z v + d * (h z v - c * h z v * h z z) = 0 := by
      linear_combination (h z v) * hcd
    rw [h0, zero_smul, sub_zero]
  have hcd : (star b)⁻¹ + b⁻¹ = (star b)⁻¹ * b⁻¹ * h z z := by
    rw [hzz]
    field_simp
    try ring
  have h₁ : τl.comp σl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show τl (σl v) = v
    rw [hτ, hσ]
    exact key _ _ hcd v
  have h₂ : σl.comp τl = LinearMap.id := by
    apply LinearMap.ext
    intro v
    show σl (τl v) = v
    rw [hσ, hτ]
    exact key _ _ (by rw [add_comm, mul_comm b⁻¹]; exact hcd) v
  refine ⟨LinearEquiv.ofLinear τl σl h₁ h₂, ?_, ?_, ?_, ?_⟩
  · show ∀ u v, h (τl u) (τl v) = h u v
    intro u v
    rw [hτ, hτ]
    have hu : h u z = star (h z u) := (hsym z u).symm
    simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, star_mul, star_inv₀, RingHom.id_apply, hu, hzz]
    field_simp
    try ring
  · show τl x = y
    rw [hτ, hzx, inv_mul_cancel₀ hb0, one_smul, hz, sub_sub_cancel]
  · intro v hxv hyv
    show τl v = v
    rw [hτ, hzv, hxv, hyv, sub_zero, mul_zero, zero_smul, sub_zero]
  · intro W hxW hyW v
    have hzW : z ∈ W := hz ▸ W.sub_mem hxW hyW
    show v ∈ W ↔ τl v ∈ W
    rw [hτ]
    constructor
    · intro hv
      exact W.sub_mem hv (W.smul_mem _ hzW)
    · intro hv
      have := W.add_mem hv (W.smul_mem (b⁻¹ * h z v) hzW)
      rwa [sub_add_cancel] at this

theorem exists_isom_scale' (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ (∀ v, h z v = 0 → ψ v = v) ∧
      ∀ W : Submodule K V, z ∈ W → ∀ v, v ∈ W ↔ ψ v ∈ W := by
  obtain ⟨ψ, hψ, hψz, hψv⟩ := exists_isom_scale hs hz hb
  refine ⟨ψ, hψ, hψz, hψv, ?_⟩
  intro W hzW v
  have hdec : h z (v - (h z v * (h z z)⁻¹) • z) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hz, sub_self]
  have hψv' : ψ v = (h z v * (h z z)⁻¹) • (b • z) + (v - (h z v * (h z z)⁻¹) • z) := by
    have e : v = (h z v * (h z z)⁻¹) • z + (v - (h z v * (h z z)⁻¹) • z) := by abel
    conv_lhs => rw [e]
    rw [map_add, map_smul, hψz, hψv _ hdec]
  constructor
  · intro hv
    rw [hψv']
    exact W.add_mem (W.smul_mem _ (W.smul_mem _ hzW)) (W.sub_mem hv (W.smul_mem _ hzW))
  · intro hv
    rw [hψv'] at hv
    have h1 := W.sub_mem hv (W.smul_mem (h z v * (h z z)⁻¹) (W.smul_mem b hzW))
    rw [add_sub_cancel_left] at h1
    have h2 := W.add_mem h1 (W.smul_mem (h z v * (h z z)⁻¹) hzW)
    rwa [sub_add_cancel] at h2

theorem exists_isom_map_of_eq_norm (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {x y : V} (hxy : h x x = h y y)
    (hx0 : h x x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hb : h x x - h y x = 0
  · have hxy' : h x x = h (-y) (-y) := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact hxy
    have hyx : h y x = h x x := by linear_combination -hb
    have hb' : h x x - h (-y) x ≠ 0 := by
      simp only [map_neg, LinearMap.neg_apply, sub_neg_eq_add]
      rw [hyx, ← two_mul]
      exact mul_ne_zero h2 hx0
    obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_move' hs hxy' hb'
    have hy0 : h y y ≠ 0 := hxy ▸ hx0
    obtain ⟨ψ, hψ, hψy, hψv, hψW⟩ := exists_isom_scale' hs hy0 (b := -1)
      (by rw [star_neg, star_one]; norm_num)
    refine ⟨ψ * τ, mul_mem hψ hτ, ?_, ?_, ?_⟩
    · show ψ (τ x) = y
      rw [hτx, map_neg, hψy, neg_one_smul, neg_neg]
    · intro v hxv hyv
      show ψ (τ v) = v
      have hyv' : h (-y) v = 0 := by
        simp only [map_neg, LinearMap.neg_apply, hyv, neg_zero]
      rw [hτv v hxv hyv', hψv v hyv]
    · intro W hxW hyW v
      show v ∈ W ↔ ψ (τ v) ∈ W
      rw [hτW W hxW (W.neg_mem hyW) v]
      exact hψW W hyW (τ v)
  · exact exists_isom_move' hs hxy hb

theorem exists_prep' (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) (hx0 : h x x ≠ 0) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
  have hφx : φ x ∈ W₂ := (hW x).1 hx
  have hn : h (φ x) (φ x) = h X X := by rw [hφ' x x]; exact hxX
  have hn0 : h (φ x) (φ x) ≠ 0 := by rw [hφ' x x]; exact hx0
  obtain ⟨τ, hτ, hτx, hτv, hτW⟩ := exists_isom_map_of_eq_norm hs h2 hn hn0
  have hτ' : ∀ a c, h (τ a) (τ c) = h a c := hτ
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, ?_, ?_⟩
  · intro v
    show v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hφx hX (φ v), ← hW v, ← hτx, hτ' (φ x) (φ v), hφ' x v]
  · intro v hv
    show τ (φ v) = φ v
    apply hτv
    · rw [hφ' x v]
      exact hv x hx
    · obtain ⟨x', rfl⟩ := φ.surjective X
      rw [hφ' x' v]
      exact hv x' ((hW x').2 hX)

theorem sd_main' [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      NondegOn h W₁ → IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => by
    rw [← starRingEnd_apply]
    exact hs.eq u v
  induction n with
  | zero =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    have hW0 : W₁ = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hr)
    refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · have h0 : v = 0 := by
        have := hM.le v hv
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0, map_zero]
      exact N.zero_mem
    · have h0 : v = 0 := by
        have := (hW v).2 (hN.le _ hv)
        rwa [hW0, Submodule.mem_bot] at this
      rw [h0]
      exact M.zero_mem
  | succ n ih =>
    intro W₁ W₂ M N φ hr hnd hM hN hφ hW
    by_cases hW0 : W₁ = ⊥
    · refine ⟨φ, hφ, fun v _ => rfl, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
      · have h0 : v = 0 := by
          have := hM.le v hv
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0, map_zero]
        exact N.zero_mem
      · have h0 : v = 0 := by
          have := (hW v).2 (hN.le _ hv)
          rwa [hW0, Submodule.mem_bot] at this
        rw [h0]
        exact M.zero_mem
    have hφ' : ∀ a c, h (φ a) (φ c) = h a c := hφ
    obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨x, hxM, hxu⟩ := IsSD.exists_unit_norm' hS hπ hs hnd hM hξ hξ0
    have hx : x ∈ W₁ := hM.le x hxM
    have hφx : φ x ∈ W₂ := (hW x).1 hx
    obtain ⟨X, hXN, hXx⟩ := IsSD.exists_norm' hS hπ hs hN hφx hxu (hφ' x x)
    have hx0 : h x x ≠ 0 := hxu.1
    have hXu : IsUnitIn S (h X X) := by
      rw [hXx]
      exact hxu
    obtain ⟨φ₁, hφ₁, hφ₁x, hφ₁W, hφ₁v⟩ := exists_prep' hs h2 hφ hW hx (hN.le X hXN) hXx.symm hx0
    have hr' : finrank K (cutW h W₁ x) ≤ n := by
      have hlt : finrank K (cutW h W₁ x) < finrank K W₁ := by
        apply Submodule.finrank_lt_finrank_of_lt
        rw [lt_iff_le_and_ne]
        refine ⟨fun v hv => (mem_cutW.1 hv).1, fun heq => ?_⟩
        have hxc : x ∈ cutW h W₁ x := by
          rw [heq]
          exact hx
        exact hx0 (mem_cutW.1 hxc).2
      omega
    obtain ⟨g, hg, hgv, hgM⟩ := ih (cutW h W₁ x) (cutW h W₂ X) (cutM h M x) (cutM h N X) φ₁ hr'
      (nondegOn_cut hnd hx hx0) (hM.cut hxM hxu) (hN.cut hXN hXu) hφ₁ hφ₁W
    have hg' : ∀ a c, h (g a) (g c) = h a c := hg
    have horth : ∀ w ∈ cutW h W₁ x, h w x = 0 := fun w hw => by
      rw [← hsym x w, (mem_cutW.1 hw).2, star_zero]
    have hgx : g x = X := by
      rw [hgv x horth, hφ₁x]
    have hdec : ∀ v : V, v = (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • x :=
      fun v => by abel
    have hgdec : ∀ v, g v = g (v - (h x v * (h x x)⁻¹) • x) + (h x v * (h x x)⁻¹) • X := fun v => by
      conv_lhs => rw [hdec v]
      rw [map_add, map_smul, hgx]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · rw [hgv v (fun w hw => hv w (mem_cutW.1 hw).1), hφ₁v v hv]
    have hxvX : h X (g v) = h x v := by
      rw [← hgx, hg']
    have hxxinv : (h x x)⁻¹ ∈ S := hxu.2.2
    constructor
    · intro hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hxM v hv) hxxinv
      have hp := proj_mem hM.toIsLatIn hxM hxu hv
      have hgp := (hgM _).1 hp
      rw [hgdec v]
      exact N.add_mem (AddSubgroup.mem_inf.1 hgp).1 (hN.smul_mem _ ha X hXN)
    · intro hv
      have hiS : h x v ∈ S := by
        rw [← hxvX]
        exact hN.int X hXN (g v) hv
      have ha : h x v * (h x x)⁻¹ ∈ S := S.mul_mem hiS hxxinv
      have hq := proj_mem hN.toIsLatIn hXN hXu hv
      rw [hxvX, hXx] at hq
      have hq' : g (v - (h x v * (h x x)⁻¹) • x) ∈ cutM h N X := by
        rw [map_sub, map_smul, hgx]
        exact hq
      have hp := (hgM _).2 hq'
      rw [hdec v]
      exact M.add_mem (AddSubgroup.mem_inf.1 hp).1 (hM.smul_mem _ ha x hxM)

end Formalism.L2.SG.Pf.G4
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open NumberField Formalism.HermitianLattices.Ext.L3

theorem local_unimodular_holds : Formalism.MainNotions.BridgeRowsGenus.LocUnimod := by
  intro F E _ _ _ _ _ _ hc S L M hL hM p hp huL huM
  have hF : IsFixF E F := fun a => by rw [hc.fixed a, RingHom.mem_range, Set.mem_range]
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hp
  have hnd : G4.NondegOn S.hT ⊤ := by
    intro ξ _ hξ0
    by_contra hcon
    push Not at hcon
    exact hξ0 (S.nondeg.2 ξ fun w => hcon w Submodule.mem_top)
  obtain ⟨g, hg, -, hgM⟩ := G4.sd_main' (WA.isHermSemilocal_locRing hc.cmUnram hp) hπ S.herm
    two_ne_zero _ ⊤ ⊤ _ _ 1 le_rfl hnd (U0.isSD_loc hL hp.isPrime huL) (U0.isSD_loc hM hp.isPrime huM)
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

end Formalism.L2.SG.Pf.Cnt
end
end
