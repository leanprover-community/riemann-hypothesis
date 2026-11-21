import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Formalism.LocalToGlobal.Columns.RecLevelLocT

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

open Classical in

theorem th_pull_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) :
    pullW (tauOfR hX hPr u w P) w = if seenC Pr u w then P.1 else conjPrime₂ P.1 := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dif_pos hw]
    rfl
  rw [e]
  by_cases hs : seenC Pr u w
  · rw [if_pos hs]
    exact (tauOfC_spec hX hPr u w hw P).resolve_right (hs.not_bar hPr _ P)
  · rw [if_neg hs]
    refine (tauOfC_spec hX hPr u w hw P).resolve_left fun h => hs (seenC_of_one hPr (τ := tauOfC w P.1) ?_)
    rw [show pullW (tauOfC w P.1) w = P.1 from h]
    exact P.2

end Gen

variable {d : ColDat} (a : ColArgs d)

open Classical in
theorem valuation_pos_iff_mem_seen (hH : HostHyp d) (u : d.what₂.Word) (w : d.what₂.places.Pl) (hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal)
    (v : {P // P ∈ d.Pr.vT u}) (x : 𝓞 d.X.E) :
    (0 : WithTop ℤ) < d.what₂.places.val w ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) ↔
      x ∈ (if decide (seenC d.Pr u (d.plEq w)) = true then v.1.asIdeal else conjIdeal (K := d.X.E) v.1.asIdeal) := by
  rw [att_val_pos d.what₂.places d.plEq hH.val_eq w]
  have h1 : d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x ∈ (d.plEq w).asIdeal ↔
      x ∈ (pullW (tauOfR d.hX d.hPr u (d.plEq w) v) (d.plEq w)).asIdeal := Iff.rfl
  rw [h1, th_pull_tauOf d.hX d.hPr u (d.plEq w) hT v]
  by_cases hs : seenC d.Pr u (d.plEq w)
  · rw [if_pos hs, if_pos (decide_eq_true hs)]
  · rw [if_neg hs, if_neg (by simpa using hs), conjIdeal_asIdeal]

theorem th_seen (hH : HostHyp d) (u : d.what₂.Word) : AtTSeen (atTTied a hH u) := by
  intro w hw v x y hy
  have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
    have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
    rw [hw] at this
    exact this
  have hy' : y = ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) := by
    apply d.what₂.embLL.injective
    rw [hy]
    show d.host.φ₀ _ = d.what₂.embLL (d.embE _)
    rw [← hH.embE_φ₀]
    rfl
  have hPv : (atTTied a hH u).Pv v = v.1.asIdeal := lv_Pv_eq a hH u v
  rw [hy', hPv]
  exact valuation_pos_iff_mem_seen hH u w hT v x

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

section K1b

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} (SG : Finset (Pl E)) (H : Subgroup (GLG E n SG)) {π : 𝓞 E}
  (v : HeightOneSpectrum (𝓞 F))

local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
local notation "𝒪v" => Formalism.BasicNotions.intV E v
local notation "pE" => algebraMap (𝓞 E) E π

variable (h : BasePi ST π)
include h

theorem thk_L_le_Sh (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero]
  refine ⟨hz.1, ?_⟩
  rw [← rll_p_mul_pinv v h (z (lastIdx n))]
  exact mul_mem (rll_incl_int v (cO E π)) (mul_mem (rll_incl_int v π) hz.2)

theorem thk_L_le_Ker (z : Fin n → Rv) (hz : z ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    z ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE / pE)) := by
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)] at hz
  rw [rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  refine ⟨hz.1, ?_⟩
  rw [div_eq_mul_inv, map_mul, mul_assoc]
  exact mul_mem (rll_incl_int v (cO E π)) hz.2

theorem thk_Row {g : GL (Fin n) Rv} (hL : g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hK : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) : rowLocalCondition n π v g := by
  refine rll_Row_of_maps n v h ?_ ?_ ?_
  · rw [← rll_baseLb_eq n h]; exact fun z hz => (hL z).1 hz
  · intro z hz
    have := add_mem (thk_L_le_Sh n v h _ (hK z hz)) hz
    rwa [sub_add_cancel] at this
  · intro z hz
    exact thk_L_le_Ker n v h _ (hK z hz)

theorem thk_inv {g : GL (Fin n) Rv} (hL : g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)))
    (hK : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹)) :
    ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  intro y hy
  have h1 := hK y hy
  rw [← rll_baseLb_eq n h] at h1 ⊢
  have h2 := ((Subgroup.inv_mem _ hL) _).1 h1
  have e : ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ ((g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y) =
      y - ((g⁻¹ : GL (Fin n) Rv) : Matrix (Fin n) (Fin n) Rv) *ᵥ y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e] at h2
  have := neg_mem h2
  rwa [neg_sub] at this

theorem thk_K_of_Row {g : GL (Fin n) Rv} (hU : g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))
    (h1 : rowLocalCondition n π v g) (h2 : rowLocalCondition n π v g⁻¹) :
    ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
      (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
  intro y hy
  have hcol := rll_col hc n v hU h2
  have hgy := rll_maps_Sh n v h h1.1 hcol y hy
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hy hgy
  rw [rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero)]
  refine ⟨fun i hi => sub_mem (hgy.1 i hi) (hy.1 i hi), ?_⟩
  have e : (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y = ((g : Matrix (Fin n) (Fin n) Rv) - 1) *ᵥ y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  show ιv pE⁻¹ * ∑ j, ((g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j - (1 : Matrix (Fin n) (Fin n) Rv) (lastIdx n) j) * y j ∈ 𝒪v
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨s, hs, e1⟩ := h1.2 j
  rw [e1, mul_assoc, rll_pinv_mul v h]
  by_cases hj : j = lastIdx n
  · subst hj
    obtain ⟨s2, hs2, e2⟩ := h2.2 (lastIdx n)
    have h3 := rll_inv_entry hc n v (Subgroup.inv_mem _ hU) (lastIdx n) (lastIdx n)
    rw [inv_inv] at h3
    rw [Matrix.one_apply_eq] at e1 e2
    have e3 : (g : Matrix (Fin n) (Fin n) Rv) (lastIdx n) (lastIdx n) - 1 =
        ιv (star pE) * sigR hc.sig (v.adicCompletion F) s2 := by
      rw [h3, sub_eq_iff_eq_add.1 e2, map_add, map_mul, map_one, rll_sigV_incl, add_sub_cancel_right]
    obtain ⟨a, b, hab⟩ := h.cop
    have hab' : ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) = 1 := by
      have h4 := congrArg (fun t => ιv (algebraMap (𝓞 E) E t)) hab
      simp only [map_add, map_mul, map_one] at h4
      exact h4
    have es : s = ιv (star pE) * (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) := by
      calc s = (ιv (algebraMap (𝓞 E) E a) * ιv pE + ιv (algebraMap (𝓞 E) E b) * ιv (star pE)) * s := by rw [hab', one_mul]
        _ = ιv (algebraMap (𝓞 E) E a) * (ιv pE * s) + ιv (algebraMap (𝓞 E) E b) * ιv (star pE) * s := by ring
        _ = ιv (algebraMap (𝓞 E) E a) * (ιv (star pE) * sigR hc.sig (v.adicCompletion F) s2) +
            ιv (algebraMap (𝓞 E) E b) * ιv (star pE) * s := by rw [← e1, e3]
        _ = _ := by ring
    rw [es]
    have e5 : ιv (star pE) * (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) *
        y (lastIdx n) = (ιv (algebraMap (𝓞 E) E a) * sigR hc.sig (v.adicCompletion F) s2 + ιv (algebraMap (𝓞 E) E b) * s) *
        (ιv (star pE) * y (lastIdx n)) := by ring
    rw [e5]
    exact mul_mem (add_mem (mul_mem (rll_incl_int v a) (rll_sigV_mem hc v hs2)) (mul_mem (rll_incl_int v b) hs)) hy.2
  · exact mul_mem hs (hy.1 j hj)

theorem localLevel_iff_kOne (hG : v ∉ plUnder F SG) (g : GL (Fin n) Rv) :
    g ∈ levLoc hc n ST SG H v ↔
      (g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ∧
        ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E)
            (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))),
          (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb E n ST)) := by
  have eD : Formalism.L2.Herm.locL v (Submodule.span (𝓞 E)
      (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))) =
      Formalism.L2.Herm.locL v (rll_dLat n (star pE)) := rll_dualV_eq hc n v h
  constructor
  · intro hg
    have hg' := hg
    rw [levLoc_eq_stabFun hc n SG H v h hG] at hg'
    obtain ⟨hL, hF⟩ := hg'
    refine ⟨hL, fun y hy => ?_⟩
    have r1 := rll_Row_of_stabFun hc n v h hL.2 hF
    have r2 := rll_Row_of_stabFun hc n v h (Subgroup.inv_mem _ hL.2) (Subgroup.inv_mem _ hF)
    rw [rll_baseLb_eq n h]
    exact thk_K_of_Row hc n v h hL.1 r1 r2 y (eD ▸ hy)
  · rintro ⟨hL, hK⟩
    have hK' : ∀ y ∈ Formalism.L2.Herm.locL v (rll_dLat n (star pE)),
        (g : Matrix (Fin n) (Fin n) Rv) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (rll_dLat n pE⁻¹) := by
      intro y hy
      rw [← rll_baseLb_eq n h]
      exact hK y (eD.symm ▸ hy)
    exact rll_mem_levLoc_of_Row hc n SG H v h hG hL.1 (thk_Row n v h hL.2 hK')
      (thk_Row n v h (Subgroup.inv_mem _ hL.2) (thk_inv n v h hL.2 hK'))

end K1b

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}

theorem th_base_companion (h : BasePi ST π) (pb : 𝓞 E) (hpb : algebraMap (𝓞 E) E pb = star (algebraMap (𝓞 E) E π)) :
    baseLb E n ST ⊔ Ideal.span {pb} • Submodule.span (𝓞 E)
      (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST)) = stdLat E n := by
  have e : Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST)) =
      rll_dLat n (star (algebraMap (𝓞 E) E π)) := rll_baseDual_eq hc n h
  rw [e]
  apply le_antisymm
  · refine sup_le (rll_baseLb_le n ST) ?_
    rw [Submodule.smul_le]
    intro r hr m hm
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    obtain ⟨h1, h2⟩ := (rll_mem_dLat n _ m).1 hm
    rw [mem_stdLat]
    intro i
    by_cases hi : i = lastIdx n
    · subst hi
      obtain ⟨t, ht⟩ := h2
      refine ⟨s * t, ?_⟩
      rw [map_mul, ht, Pi.smul_apply, Algebra.smul_def, map_mul, hpb, mul_assoc]
    · obtain ⟨t, ht⟩ := h1 i hi
      refine ⟨s * pb * t, ?_⟩
      rw [map_mul, ht, Pi.smul_apply, Algebra.smul_def]
  · intro x hx
    rw [mem_stdLat] at hx
    choose r hr using hx
    have hs0 : star (algebraMap (𝓞 E) E π) ≠ 0 := h.star_ne_zero
    have e1 : x = (x - Pi.single (lastIdx n) (x (lastIdx n))) +
        pb • (Pi.single (lastIdx n) ((star (algebraMap (𝓞 E) E π))⁻¹ * x (lastIdx n)) : Fin n → E) := by
      funext i
      by_cases hi : i = lastIdx n
      · subst hi
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply, sub_self, zero_add]
        rw [Algebra.smul_def, hpb, mul_inv_cancel_left₀ hs0]
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hi, Pi.smul_apply, sub_zero, smul_zero, add_zero]
    rw [e1]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pb) ?_)
    · rw [rll_baseLb_eq n h, rll_mem_dLat]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, sub_zero]
        exact ⟨r i, hr i⟩
      · rw [Pi.sub_apply, Pi.single_eq_same, sub_self, mul_zero]
        exact zero_mem _
    · rw [rll_mem_dLat]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hi]
        exact zero_mem _
      · rw [Pi.single_eq_same, mul_inv_cancel_left₀ hs0]
        exact ⟨r _, hr _⟩

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

include hX hPr in

theorem localLevelIsKOneAtT_holds : LocalLevelIsKOneAtT hc u Λ := fun v hv x =>
  localLevel_iff_kOne hc n Pr.vGs Λ.grp v (basePi_of_ok hX hPr u) (rls_T_notUnder hPr u v hv) x

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem th_reL_std {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) :
    Formalism.L2.Forms.reL h (stdLat E a) = stdLat E b := by
  subst h
  exact Formalism.L2.Forms.reL_rfl _

theorem levPack_base (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (pb : 𝓞 X.E)
    (hpb : algebraMap (𝓞 X.E) X.E pb = star (algebraMap (𝓞 X.E) X.E (Pr.piT u))) :
    (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 X.E)
      (dualSet (hc.sig : X.E →+* X.E) H.J (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb) = stdLat X.E H.n' := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_base_companion hc _ (basePi_of_ok hX hPr u) pb hpb

end Gen

theorem th_map_span_std {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r r' : ℕ} (e : V ≃ₗ[E] (Fin r → E)) (b : Fin r' → V) (σ : Fin r' ≃ Fin r)
    (hb : ∀ a, e (b a) = Pi.single (σ a) (1 : E)) :
    (Submodule.span (𝓞 E) (Set.range b)).map ((e : V →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E)) = stdLat E r := by
  rw [Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show e (b a) ∈ _
    rw [hb]
    simpa using single_mem_stdLat (E := E) (σ a) 1
  · intro x hx
    rw [mem_stdLat] at hx
    choose t ht using hx
    have hsum : x = ∑ j, t j • e (b (σ.symm j)) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one, ht]
      · intro j _ hj
        rw [hb, Equiv.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable {d : ColDat}

theorem localLevelIsKOne_everywhere (d : ColDat) : LocalLevelIsKOneEverywhere d := fun u i => localLevelIsKOneAtT_holds d.sp.cm d.hX d.hPr u (d.lev i)

theorem coordLattice_selfDual_eq_std (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.sp.X i).L0 = stdLat d.X.E (d.sp.X i).rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_X i hi]
  refine th_map_span_std (Formalism.L2.Herm.crd (d.sp.X i)) _ (Equiv.refl _) fun a => ?_
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem coordLattice_selfDual_zero (hS : SpStd d.toColBase) : d.sp.crdLat0 (d.sp.X 0).L0 = stdLat d.X.E d.R.k := by
  unfold Spaces.crdLat0
  rw [hS.selfDual_span_frame_X 0 (Nat.zero_le _)]
  refine th_map_span_std d.sp.crd0 _ (finCongr d.sp.rank0) fun a => ?_
  funext j
  show (d.sp.X 0).frame.equivFun ((d.sp.X 0).frame a) ((finCongr d.sp.rank0).symm j) = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [h, Equiv.symm_apply_apply]⟩

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

structure AtTOwed (hS : SpStd d.toColBase) (hH : HostHyp d) where
  disc : ∀ u, AtTDisc (d.colRec a) u
  moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)
  xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)

def hermAtT (hS : SpStd d.toColBase) (hH : HostHyp d) (O : AtTOwed a hS hH) (u : d.what₂.Word) :
    CH.AtT (d.colRec a) u (tieEV d.sp.cm d.hX d.hPr u) (fun v => tieFv d.sp.cm d.hX d.hPr u v) :=
  atTOf (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) (fun v => tieFv d.sp.cm d.hX d.hPr u v)
    (fun v x => tieFv_mk d.sp.cm d.hX d.hPr u v x) (th_seen a hH u) (O.disc u) (O.moves u) (O.xp u)

section Asm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
  (O : AtTOwed a hS hH)

theorem cofTied : CH.CofTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u
  show (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E) * (d.piT u : d.host.E) = (d.piT d.u₀ : d.host.E)
  exact div_mul_cancel₀ _ (basePi_of_ok d.hX d.hPr u).coe_ne_zero

theorem baseTied : CH.BaseTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u pb hpb
  have hpb' : algebraMap (𝓞 d.X.E) d.X.E pb = star (algebraMap (𝓞 d.X.E) d.X.E (d.Pr.piT u)) := by
    rw [att_star_eq]
    exact hpb
  refine ⟨?_, fun i h1 hm => ?_⟩
  · rw [coordLattice_selfDual_zero hS]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) _ _ _ _ (hK u 0) (hCrd0 hS u) pb hpb'
  · rw [coordLattice_selfDual_eq_std hS i hm]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) _ _ _ _ (hK u i) (hCrd hS u i hm) pb hpb'

structure HermOwed where
  levelZeroCompatibility : CH.Lev0Tied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  ad : CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  piG : CH.PiGConst (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) levelZeroCompatibility
  stabMap : CH.StabMapTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  fvI : CH.FvStepTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)

def colsHerm (W : HermOwed a hS hH hP hK S hI O) : CH.ColsHerm (d.colRec a) where
  base := hermCols a hS hP hK S hI
  atT := hermAtT a hS hH O
  levelZeroCompatibility := W.levelZeroCompatibility
  ad := W.ad
  cof := cofTied a hS hH hP hK S hI O
  piG := W.piG
  stabMap := W.stabMap
  fvI := W.fvI
  std := stdTied a hS
  baseL := baseTied a hS hH hP hK S hI O

end Asm

end Formalism.L2.Col
end
end
