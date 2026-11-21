import Formalism.WachLatticeTwists.TorsionKernelSplitting.Statement
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveTopHolds
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
import Formalism.WachLatticeTwists.TorsionLengthCounts.CardFilterAddLeOfNone
import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremHZero
import Formalism.WachLatticeTwists.TorsionKernelSplitting.WachTwistSplitTheoremStatedForm

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem rowCost : StatRowCost := by
  intro O _ _ _ Cs _ _ Fs Im rr _ ℓ e c J hfin hlift hH0 hrk
  have hcol := Formalism.RepresentationBoundsCohomology.rowColength O Fs (Im.comap Fs.subtype) ℓ e
    (fun x => by
      rw [Submodule.mem_comap]
      exact hlift x.1 x.2)
  obtain ⟨H, hHk, hHt⟩ := hH0
  have htor := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O rr H ℓ c hHk
  refine hcol.trans ?_
  have hrk' : (Module.finrank O Fs : ℕ∞) ≤ (J : ℕ∞) := by exact_mod_cast hrk
  gcongr
  exact hHt.trans htor

theorem splitFold : StatSplitFold := by
  intro v what₂ cols conj lenRow a x c h y₁ y₂ j J R hk hrows hj hL
  refine hk.trans ?_
  have h1 : ∑ w ∈ what₂, lenRow w ≤ ∑ w ∈ cols, lenRow (conj w) := by
    rw [hrows]
    exact Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)
  have h2 : ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w) ≤
      ∑ w ∈ cols, (a w + (J w : ℕ∞) * x w + c w + h w + y₁ w + y₂ w) := by
    calc ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w)
        ≤ ∑ w ∈ cols, lenRow (conj w) + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w) :=
          add_le_add h1 le_rfl
      _ = ∑ w ∈ cols, ((a w + (j w : ℕ∞) * x w + c w + h w) + lenRow (conj w)) := by
          rw [add_comm, ← Finset.sum_add_distrib]
      _ ≤ ∑ w ∈ cols, (a w + (J w : ℕ∞) * x w + c w + h w + y₁ w + y₂ w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [add_assoc (a w + (J w : ℕ∞) * x w + c w + h w)]
          have hjw : (j w : ℕ∞) ≤ (J w : ℕ∞) := by exact_mod_cast hj w hw
          have hLw := hL w hw
          gcongr
  gcongr

end Formalism.RepresentationBoundsCohomology.JS
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem finSub : StatFinSub := by
  intro O _ _ _ Cs _ _ Fs hfin
  infer_instance

theorem torsion_le_h_zero : TorsionLeHZero := by
  intro O _ _ _ D _ T₂ V A Cs _ _ _ _ _ _ _ _ _ _ ρ₂ ρV ρA i q Zc cls Fs hseq hcls
  obtain ⟨hi, hex, hiE, hqE⟩ := hseq
  obtain ⟨hadd, hsmul, hB, hFs⟩ := hcls
  let clsL : Zc →ₗ[O] Cs :=
    { toFun := fun a => cls a.1
      map_add' := fun a b => hadd a.1 a.2 b.1 b.2
      map_smul' := fun c a => hsmul c a.1 a.2 }
  let Γ : Submodule O (Zc × V) :=
    { carrier := {p | ∀ g, i ((p.1 : D → T₂) g) = ρV g p.2 - p.2}
      add_mem' := by
        intro p p' hp hp' g
        have h1 := hp g
        have h2 := hp' g
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, map_add, h1, h2]
        abel
      zero_mem' := by
        intro g
        simp
      smul_mem' := by
        intro c p hp g
        have h1 := hp g
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, map_smul, h1,
          smul_sub] }
  let f : Γ →ₗ[O] Cs := clsL ∘ₗ LinearMap.fst O Zc V ∘ₗ Γ.subtype
  let g : Γ →ₗ[O] A := q ∘ₗ LinearMap.snd O Zc V ∘ₗ Γ.subtype
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hq : q p.1.2 = 0 := hp
    obtain ⟨t, ht⟩ := (hex _).1 hq
    show cls (p.1.1 : D → T₂) = 0
    rw [hB _ p.1.1.2]
    refine ⟨t, funext fun γ => hi ?_⟩
    have h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2 := p.2 γ
    rw [h1, ← ht]
    show i (ρ₂ γ t - t) = _
    rw [map_sub, hiE γ t]
  have hg : LinearMap.range g ≤ LinearMap.ker (coD0 ρA) := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    funext γ
    show ρA γ (q p.1.2) - q p.1.2 = 0
    rw [← hqE γ, ← map_sub]
    have h1 : i ((p.1.1 : D → T₂) γ) = ρV γ p.1.2 - p.1.2 := p.2 γ
    rw [← h1]
    exact (hex _).2 ⟨_, rfl⟩
  have hT : (Submodule.torsion O Fs).map Fs.subtype ≤ LinearMap.range f := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff x).1 hx
    obtain ⟨a, ha, hxa⟩ := hFs x.1 x.2
    have hc0 : (c : O) ≠ 0 := nonZeroDivisors.ne_zero c.2
    have hcx : (c : O) • (x : Cs) = 0 := by
      have h := congrArg (Subtype.val) hc
      exact h
    have h0 : cls ((c : O) • a) = 0 := by rw [hsmul _ a ha, ← hxa, hcx]
    obtain ⟨t, ht⟩ := (hB _ (Zc.smul_mem _ ha)).1 h0
    have hcK : algebraMap O (FractionRing O) (c : O) ≠ 0 := by
      simp [hc0]
    let v : V := (algebraMap O (FractionRing O) (c : O))⁻¹ • i t
    have hv : (c : O) • v = i t := by
      show (c : O) • ((algebraMap O (FractionRing O) (c : O))⁻¹ • i t) = i t
      rw [← algebraMap_smul (FractionRing O) (c : O), smul_smul, mul_inv_cancel₀ hcK, one_smul]
    have hinj : ∀ y : V, (c : O) • y = 0 → y = 0 := by
      intro y hy
      rw [← algebraMap_smul (FractionRing O) (c : O)] at hy
      exact (smul_eq_zero.1 hy).resolve_left hcK
    have hmem : ((⟨a, ha⟩ : Zc), v) ∈ Γ := by
      intro γ
      show i (a γ) = ρV γ v - v
      have h2 : (c : O) • (i (a γ) - (ρV γ v - v)) = 0 := by
        rw [smul_sub, smul_sub, ← map_smul, ← map_smul, hv, ← hiE γ t, ← map_sub]
        have h3 : ρ₂ γ t - t = ((c : O) • a) γ := congrFun ht γ
        rw [h3, Pi.smul_apply, sub_self]
      exact sub_eq_zero.1 (hinj _ h2)
    exact ⟨⟨_, hmem⟩, hxa.symm⟩
  calc Module.length O (Submodule.torsion O Fs)
      = Module.length O ((Submodule.torsion O Fs).map Fs.subtype) :=
        (Submodule.equivMapOfInjective Fs.subtype Fs.injective_subtype _).length_eq
    _ ≤ Module.length O (LinearMap.range f) :=
        Module.length_le_of_injective (Submodule.inclusion hT) (Submodule.inclusion_injective hT)
    _ ≤ Module.length O (Γ ⧸ LinearMap.ker g) := by
        have hker' : LinearMap.ker g ≤ LinearMap.ker f.rangeRestrict := by
          rw [LinearMap.ker_rangeRestrict]
          exact hker
        refine Module.length_le_of_surjective ((LinearMap.ker g).liftQ f.rangeRestrict hker') ?_
        rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]
    _ = Module.length O (LinearMap.range g) := g.quotKerEquivRange.length_eq
    _ ≤ Module.length O (LinearMap.ker (coD0 ρA)) :=
        Module.length_le_of_injective (Submodule.inclusion hg) (Submodule.inclusion_injective hg)

end Formalism.RepresentationBoundsCohomology.JS
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem IsLatSeq.res {O G T₂ V A : Type*} [CommRing O] [Group G] [AddCommGroup T₂] [Module O T₂]
    [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A]
    {ρ₂ : Representation O G T₂} {ρV : Representation O G V} {ρA : Representation O G A}
    {i : T₂ →ₗ[O] V} {q : V →ₗ[O] A} (h : IsLatSeq ρ₂ ρV ρA i q) (D : Subgroup G) :
    IsLatSeq (resRep ρ₂ D) (resRep ρV D) (resRep ρA D) i q :=
  ⟨h.1, h.2.1, fun g m => h.2.2.1 (g : G) m, fun g m => h.2.2.2 (g : G) m⟩

end Formalism.RepresentationBoundsCohomology.JS
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem rankLe : StatRankLe := by
  intro O _ _ _ Cs HV _ _ _ _ _ _ jT Fs Hf hfin hpre hker
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank
    (R := O) (M := Fs) le_rfl

  have hli2 : LinearIndependent O (fun x : s => jT ((x : Fs) : Cs)) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc k
    have h1 : jT ((∑ x : s, c x • (x : Fs) : Fs) : Cs) = 0 := by
      rw [← hc]
      simp
    obtain ⟨a, ha0, ha⟩ := hker _ (∑ x : s, c x • (x : Fs) : Fs).2 h1
    have h2 : ∑ x : s, (a * c x) • (x : Fs) = 0 := by
      have h4 : a • (∑ x : s, c x • (x : Fs) : Fs) = 0 := Subtype.ext ha
      rw [← h4, Finset.smul_sum]
      exact Finset.sum_congr rfl fun x _ => mul_smul _ _ _
    have h3 := hli (fun x => a * c x) h2 k
    exact (mul_eq_zero.1 h3).resolve_left ha0
  have hli3 : LinearIndependent (FractionRing O) (fun x : s => jT ((x : Fs) : Cs)) :=
    hli2.localization (FractionRing O) (nonZeroDivisors O)
  have hli4 : LinearIndependent (FractionRing O)
      (fun x : s => (⟨jT ((x : Fs) : Cs), hpre _ (x : Fs).2⟩ : Hf)) := by
    refine LinearIndependent.of_comp Hf.subtype ?_
    exact hli3
  have := hli4.fintype_card_le_finrank
  rw [Fintype.card_coe, hs] at this
  exact this

theorem kerTors : StatKerTors := by
  intro O _ _ _ D _ T₂ V A Cs HV _ _ _ _ _ _ _ _ _ _ ρ₂ ρV ρA i q Zc cls Fs clsV jT hseq hcls
    htor hj hV x hx hx0
  obtain ⟨hi, hex, hiE, hqE⟩ := hseq
  obtain ⟨hadd, hsmul, hB, hFs⟩ := hcls
  obtain ⟨a, ha, rfl⟩ := hFs x hx
  rw [hj a ha] at hx0
  obtain ⟨v, hv⟩ := hV a ha hx0
  obtain ⟨c, hc0, hc⟩ := htor (q v)
  rw [← map_smul] at hc
  obtain ⟨t, ht⟩ := (hex _).1 hc
  refine ⟨c, hc0, ?_⟩
  rw [← hsmul c a ha, hB _ (Zc.smul_mem c ha)]
  refine ⟨t, funext fun γ => hi ?_⟩
  show i (ρ₂ γ t - t) = i (c • a γ)
  have h1 : ρV γ v - v = i (a γ) := congrFun hv γ
  rw [map_sub, hiE γ t, ht, map_smul, map_smul, ← h1, smul_sub]

end Formalism.RepresentationBoundsCohomology.JS
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem ko_pi_torsion (O : Type) [CommRing O] [IsDomain O] (rr : Type) [Fintype rr]
    (z : rr → KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  have h1 : ∀ k, ∃ c : O, c ≠ 0 ∧ c • z k = 0 := by
    intro k
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z k)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨a, ?_⟩
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero hb
    rw [Algebra.smul_def, mul_div_cancel₀ _ hb0]
  choose c hc0 hc using h1
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.2 fun k _ => hc0 k, funext fun k => ?_⟩
  rw [Pi.smul_apply, ← Finset.mul_prod_erase univ c (Finset.mem_univ k), mul_comm, mul_smul, hc k,
    smul_zero]
  rfl

end Formalism.RepresentationBoundsCohomology.JS
end
end
