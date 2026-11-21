import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernels

section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeValues

section Gen

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem g_self (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i : L.ι} (hi : f y ∈ L.U i) :
    gm f y (L.U i ⊓ L.U i) (L.g i i) = 1 :=
  mul_eq_left.1 (gm_cocycle hL f y hi hi hi)

theorem mem_twoPullbackChart_iff {φ : Fin 2 → (Y ⟶ X)} (r : Z ⟶ Y) (z : Z) (a b : L.ι) :
    r z ∈ LB.wchart L φ ![a, b] ↔ (r ≫ φ 0) z ∈ L.U a ∧ (r ≫ φ 1) z ∈ L.U b := by
  constructor
  · intro h
    exact ⟨Set.mem_iInter.1 h 0, Set.mem_iInter.1 h 1⟩
  · rintro ⟨h0, h1⟩
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    exacts [h0, h1]

theorem gv_trans {φ : Fin 2 → (Y ⟶ X)} {ε : Fin 2 → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r : Z ⟶ Y) (z : Z) {a b a' b' : L.ι} (h : r z ∈ LB.wchart L φ ![a, b])
    (h' : r z ∈ LB.wchart L φ ![a', b']) :
    gm r z (LB.wchart L φ ![a, b]) (t.s ![a, b]) =
      gm (r ≫ φ 0) z (L.U a ⊓ L.U a') (L.g a a') ^ ε 0 * gm (r ≫ φ 1) z (L.U b ⊓ L.U b') (L.g b b') ^ ε 1 *
        gm r z (LB.wchart L φ ![a', b']) (t.s ![a', b']) := by
  rw [gen_trans ht r z h h', trF, Fin.prod_univ_two]
  rfl

theorem pullbackGenerator_chart_transition {f : Y ⟶ X} {t : LB.Gen (L.pull f)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z) {a a' : L.ι}
    (h : (r ≫ f) z ∈ L.U a) (h' : (r ≫ f) z ∈ L.U a') :
    gm r z ((L.pull f).U (fun _ => a)) (t.s (fun _ => a)) =
      gm (r ≫ f) z (L.U a ⊓ L.U a') (L.g a a') * gm r z ((L.pull f).U (fun _ => a')) (t.s (fun _ => a')) := by
  refine (gen_trans ht r z (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h')).trans ?_
  rw [trF, Fintype.prod_unique, zpow_one]
  rfl

theorem pullbackPowerSection_chart_transition {f : Y ⟶ X} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => f) (fun _ => 1))) (r : Z ⟶ Y) (z : Z)
    {a a' : L.ι} (h : (r ≫ f) z ∈ L.U a) (h' : (r ≫ f) z ∈ L.U a') :
    gs r z (LB.wchart L (fun _ : Fin 1 => f) (fun _ => a)) (s.f (fun _ => a)) =
      (gm (r ≫ f) z (L.U a ⊓ L.U a') (L.g a a')).val *
        gs r z (LB.wchart L (fun _ : Fin 1 => f) (fun _ => a')) (s.f (fun _ => a')) := by
  rw [sec_trans s r z (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h'), trF, Fin.prod_univ_one,
    zpow_one]

end Gen

section Pts

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {x : Sp ℂ ⟶ S}

abbrev rpt (a : Over.mk x ⟶ A) : Sp ℂ ⟶ (Over.mk x ⊗ A).left := (lift (𝟙 (Over.mk x)) a).left

abbrev pl (a : Over.mk x ⟶ A) : Sp ℂ ⟶ A.left := a.left

theorem rpt_snd (a : Over.mk x ⟶ A) : rpt a ≫ (snd (Over.mk x) A).left = pl a := lift_l_snd _ _

theorem rpt_mulT (a : Over.mk x ⟶ A) (p : ℕ) : rpt a ≫ (mulT A (Over.mk x) p).left = rpt (a ^ p) := by
  rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]

theorem rpt_transl (a c : Over.mk x ⟶ A) : rpt a ≫ (translT A c).left = rpt (c * a) := by
  rw [← Over.comp_left, lift_transl, Category.id_comp]

end Pts

section Core

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : RigLB A) {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2)))

def kc (a : Over.mk x ⟶ A) : L.L.ι := (exists_chart L.isLB (a.left cpt)).choose

theorem kc_mem (a : Over.mk x ⟶ A) : pl a cpt ∈ L.L.U (kc L a) := (exists_chart L.isLB (a.left cpt)).choose_spec

def W (r : Sp ℂ ⟶ (Over.mk x ⊗ A).left) (k j i : L.L.ι) : ((Sp ℂ).presheaf.stalk cpt)ˣ :=
  gm r cpt (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![k, j]) (β₀.s ![k, j]) *
    (gm r cpt (LB.wchart L.L (isoφ A Ψ) ![k, i]) (β.s ![k, i]))⁻¹

variable {L β β₀}

theorem fiberComplexPoint_mem_thetaTraceChart_of_mem (a : Over.mk x ⟶ A) {k j : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hj : pl (a ^ p) cpt ∈ L.L.U j) :
    rpt a cpt ∈ LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![k, j] := by
  refine (mem_twoPullbackChart_iff _ _ _ _).2 ⟨?_, ?_⟩
  · show (rpt a ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [rpt_snd]; exact hk
  · show (rpt a ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [← Category.assoc, rpt_mulT, rpt_snd]; exact hj

theorem fiberComplexPoint_mem_thetaTraceIsoChart_of_comp (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa) {k i : L.L.ι}
    (hk : pl a cpt ∈ L.L.U k) (hi : pl ψa cpt ∈ L.L.U i) :
    rpt a cpt ∈ LB.wchart L.L (isoφ A Ψ) ![k, i] := by
  refine (mem_twoPullbackChart_iff _ _ _ _).2 ⟨?_, ?_⟩
  · show (rpt a ≫ (snd (Over.mk x) A).left) cpt ∈ _
    rw [rpt_snd]; exact hk
  · show (rpt a ≫ Ψ ≫ (snd (Over.mk x') A).left) cpt ∈ _
    rw [← Category.assoc, ha, rpt_snd]; exact hi

theorem W_trans (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {k j i k' j' i' : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hk' : pl a cpt ∈ L.L.U k')
    (hj : pl (a ^ p) cpt ∈ L.L.U j) (hj' : pl (a ^ p) cpt ∈ L.L.U j')
    (hi : pl ψa cpt ∈ L.L.U i) (hi' : pl ψa cpt ∈ L.L.U i') :
    W L β β₀ (rpt a) k j i * gm (pl (a ^ p)) cpt (L.L.U j ⊓ L.L.U j') (L.L.g j j') =
      gm (pl ψa) cpt (L.L.U i ⊓ L.L.U i') (L.L.g i i') * W L β β₀ (rpt a) k' j' i' := by
  have e0 : rpt a ≫ isoφ A (mulT A (Over.mk x) p).left 0 = pl a := rpt_snd a
  have e0' : rpt a ≫ isoφ A Ψ 0 = pl a := rpt_snd a
  have e1 : rpt a ≫ isoφ A (mulT A (Over.mk x) p).left 1 = pl (a ^ p) := by
    show rpt a ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left = _
    rw [← Category.assoc, rpt_mulT, rpt_snd]
  have f1 : rpt a ≫ isoφ A Ψ 1 = pl ψa := by
    show rpt a ≫ Ψ ≫ (snd (Over.mk x') A).left = _
    rw [← Category.assoc, ha, rpt_snd]
  unfold W
  rw [gv_trans hβ₀ (rpt a) cpt (fiberComplexPoint_mem_thetaTraceChart_of_mem a hk hj) (fiberComplexPoint_mem_thetaTraceChart_of_mem a hk' hj'),
    gv_trans hβ (rpt a) cpt (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp a ψa ha hk hi) (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp a ψa ha hk' hi'), e0, e0', e1, f1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  abel

end Core

section Vals

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : RigLB A) {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  (β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))) (β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2)))

def bv (i j : L.L.ι) (a : Over.mk x ⟶ A) : ℂ := ev (W L β β₀ (rpt a) (kc L a) j i).val

variable {L β β₀}

theorem bv_ne (i j : L.L.ι) (a : Over.mk x ⟶ A) : bv L β β₀ i j a ≠ 0 :=
  ((W L β β₀ (rpt a) (kc L a) j i).isUnit.map ev).ne_zero

theorem W_eq (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {k j i : L.L.ι} (hk : pl a cpt ∈ L.L.U k) (hj : pl (a ^ p) cpt ∈ L.L.U j) (hi : pl ψa cpt ∈ L.L.U i) :
    W L β β₀ (rpt a) k j i = W L β β₀ (rpt a) (kc L a) j i := by
  have e := W_trans hβ hβ₀ a ψa ha hk (kc_mem L a) hj hj hi hi
  rwa [g_self L.isLB _ _ hj, g_self L.isLB _ _ hi, _root_.mul_one, _root_.one_mul] at e

theorem bv_trans (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa)
    {i j i' j' : L.L.ι} (hi : pl ψa cpt ∈ L.L.U i) (hi' : pl ψa cpt ∈ L.L.U i')
    (hj : pl (a ^ p) cpt ∈ L.L.U j) (hj' : pl (a ^ p) cpt ∈ L.L.U j') :
    bv L β β₀ i j a * valAt' (pl (a ^ p)) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val =
      valAt' (pl ψa) (L.L.U i ⊓ L.L.U i') (L.L.g i i').val * bv L β β₀ i' j' a := by
  have e := congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val)
    (W_trans hβ hβ₀ a ψa ha (kc_mem L a) (kc_mem L a) hj hj' hi hi')
  simp only [Units.val_mul, map_mul] at e
  rw [ev_gm (pl (a ^ p)) (L.L.U j ⊓ L.L.U j') ⟨hj, hj'⟩, ev_gm (pl ψa) (L.L.U i ⊓ L.L.U i') ⟨hi, hi'⟩] at e
  exact e

end Vals

section Sum

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem bv_values (hβ : β.IsGen) (hβ₀ : β₀.IsGen) {s : LB.Sec (LPow A L.L 1 (Over.mk x))}
    {s₁ : LB.Sec (LPow A L.L ((p : ℤ) ^ 2) (Over.mk x))} {s' : LB.Sec (LPow A L.L 1 (Over.mk x'))}
    (hc₀ : IsCarried A L (mulT A (Over.mk x) p).left _ β₀ s s₁) {n : ℕ} (cr : Fin n → (Over.mk x ⟶ A))
    (hcr : ∀ m, cr m ∈ transKer A Ψ)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk x ⊗ A).left) (z : Z) (J), Good L.L z J →
      sv A L s' (r ≫ Ψ) z J = ∑ i, ((val β (r ≫ (translT A (cr i)).left) z J)⁻¹).val *
        sv A L s₁ (r ≫ (translT A (cr i)).left) z J)
    (a : Over.mk x ⟶ A) (ψa : Over.mk x' ⟶ A) (ha : rpt a ≫ Ψ = rpt ψa) (i : L.L.ι) (jm : Fin n → L.L.ι)
    (hi : pl ψa cpt ∈ L.L.U i) (hj : ∀ m, pl ((cr m * a) ^ p) cpt ∈ L.L.U (jm m)) :
    valAt' (rpt ψa) ((LPow A L.L 1 (Over.mk x')).U (fun _ => i)) (s'.f (fun _ => i)) =
      ∑ m, bv L β β₀ i (jm m) (cr m * a) *
        valAt' (rpt ((cr m * a) ^ p)) ((LPow A L.L 1 (Over.mk x)).U (fun _ => jm m)) (s.f (fun _ => jm m)) := by
  obtain ⟨J, hJ, hJi⟩ := exists_good L.L L.isLB cpt (fun _ : Unit => pl ψa) (fun _ => i) (fun _ _ _ => rfl)
    (fun _ => hi)
  have H := hv _ (rpt a) cpt J hJ
  rw [ha] at H
  have hl : sv A L s' (rpt ψa) cpt J =
      gs (rpt ψa) cpt ((LPow A L.L 1 (Over.mk x')).U (fun _ => i)) (s'.f (fun _ => i)) :=
    sval_of _ _ _ _ _ fun _ => (congrArg J (rpt_snd ψa)).trans (hJi ())
  have ml : rpt ψa cpt ∈ (LPow A L.L 1 (Over.mk x')).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => by
      show (rpt ψa ≫ (snd (Over.mk x') A).left) cpt ∈ L.L.U i
      rw [rpt_snd]; exact hi
  rw [← ev_gs (rpt ψa) _ ml (s'.f fun _ => i), ← hl, H, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rpt_transl]
  set c := cr m * a with hc
  have hcΨ : rpt c ≫ Ψ = rpt ψa := by
    rw [hc, ← rpt_transl, Category.assoc, mem_transKer.1 (hcr m), ha]
  have hmul : rpt c ≫ (mulT A (Over.mk x) p).left = rpt (c ^ p) := rpt_mulT c p
  rw [hc₀.val _ cpt hJ, hmul]
  have v0 : val β₀ (rpt c) cpt J = gm (rpt c) cpt
      (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![J (pl c), J (pl (c ^ p))])
      (β₀.s ![J (pl c), J (pl (c ^ p))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd c)
      · show J (rpt c ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) = _
        rw [← Category.assoc, hmul, rpt_snd]; rfl
  have v1 : val β (rpt c) cpt J =
      gm (rpt c) cpt (LB.wchart L.L (isoφ A Ψ) ![J (pl c), i]) (β.s ![J (pl c), i]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd c)
      · show J (rpt c ≫ Ψ ≫ (snd (Over.mk x') A).left) = _
        rw [← Category.assoc, hcΨ, rpt_snd]; exact hJi ()
  have s0 : sv A L s (rpt (c ^ p)) cpt J = gs (rpt (c ^ p)) cpt
      ((LPow A L.L 1 (Over.mk x)).U (fun _ => J (pl (c ^ p)))) (s.f (fun _ => J (pl (c ^ p)))) :=
    sval_of _ _ _ _ _ fun _ => congrArg J (rpt_snd _)
  have hk : pl c cpt ∈ L.L.U (J (pl c)) := hJ _
  have hj' : pl (c ^ p) cpt ∈ L.L.U (J (pl (c ^ p))) := hJ _
  have et := W_trans hβ hβ₀ c ψa hcΨ hk (kc_mem L c) hj' (hj m) hi hi
  rw [g_self L.isLB _ _ hi, _root_.one_mul] at et
  have st : gs (rpt (c ^ p)) cpt ((LPow A L.L 1 (Over.mk x)).U (fun _ => J (pl (c ^ p))))
      (s.f (fun _ => J (pl (c ^ p)))) =
      (gm (pl (c ^ p)) cpt (L.L.U (J (pl (c ^ p))) ⊓ L.L.U (jm m)) (L.L.g (J (pl (c ^ p))) (jm m))).val *
        gs (rpt (c ^ p)) cpt ((LPow A L.L 1 (Over.mk x)).U (fun _ => jm m)) (s.f (fun _ => jm m)) := by
    have e := pullbackPowerSection_chart_transition (f := (snd (Over.mk x) A).left) s (rpt (c ^ p)) cpt (a := J (pl (c ^ p))) (a' := jm m)
      (by rw [rpt_snd]; exact hj') (by rw [rpt_snd]; exact hj m)
    rw [rpt_snd] at e
    exact e
  have mj : rpt (c ^ p) cpt ∈ (LPow A L.L 1 (Over.mk x)).U (fun _ => jm m) :=
    Set.mem_iInter.2 fun _ => by
      show (rpt (c ^ p) ≫ (snd (Over.mk x) A).left) cpt ∈ L.L.U (jm m)
      rw [rpt_snd]; exact hj m
  rw [s0, v0, v1, bv, ← ev_gs _ _ mj (s.f fun _ => jm m), ← map_mul, ← et]
  unfold W
  simp only [Units.val_mul]
  rw [st]
  ring_nf

end Sum

section Hol

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem ev_inv (u : ((Sp ℂ).presheaf.stalk cpt)ˣ) : ev (u⁻¹).val = (ev u.val)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem bv_hol (hβ : β.IsGen) (hβ₀ : β₀.IsGen) (ψp : (Over.mk x ⟶ A) → (Over.mk x' ⟶ A))
    (hΨ : ∀ a, rpt a ≫ Ψ = rpt (ψp a)) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk x ⟶ A))
    (he : IsHolTo Set.univ (fun w => rpt (e w))) (i j : L.L.ι) :
    DifferentiableOn ℂ (fun w => bv L β β₀ i j (e w))
      {w | ⊤ ≤ pl (ψp (e w)) ⁻¹ᵁ L.L.U i ∧ ⊤ ≤ pl (e w ^ p) ⁻¹ᵁ L.L.U j} := by
  intro w₀ hw₀
  obtain ⟨o₀, d₀⟩ := he (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j])
    (β₀.s ![kc L (e w₀), j]).val
  obtain ⟨o₁, d₁⟩ := he (LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]) (β.s ![kc L (e w₀), i]).val
  have hN := o₀.inter o₁
  have key : ∀ w ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ
        LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j]} ∩
      {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]},
      bv L β β₀ i j (e w) =
        valAt' (rpt (e w)) (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j])
            (β₀.s ![kc L (e w₀), j]).val *
          (valAt' (rpt (e w)) (LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]) (β.s ![kc L (e w₀), i]).val)⁻¹ := by
    rintro w ⟨⟨-, h0⟩, ⟨-, h1⟩⟩
    have m0 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j] :=
      (mem_iff _ _).2 h0
    have m1 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i] := (mem_iff _ _).2 h1
    obtain ⟨a0, a1⟩ := (mem_twoPullbackChart_iff _ _ _ _).1 m0
    obtain ⟨-, b1⟩ := (mem_twoPullbackChart_iff _ _ _ _).1 m1
    have hk : pl (e w) cpt ∈ L.L.U (kc L (e w₀)) := by
      rwa [show rpt (e w) ≫ isoφ A (mulT A (Over.mk x) p).left 0 = pl (e w) from rpt_snd _] at a0
    have hj : pl (e w ^ p) cpt ∈ L.L.U j := by
      rwa [show rpt (e w) ≫ isoφ A (mulT A (Over.mk x) p).left 1 = pl (e w ^ p) by
        show rpt (e w) ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left = _
        rw [← Category.assoc, rpt_mulT, rpt_snd]] at a1
    have hi : pl (ψp (e w)) cpt ∈ L.L.U i := by
      rwa [show rpt (e w) ≫ isoφ A Ψ 1 = pl (ψp (e w)) by
        show rpt (e w) ≫ Ψ ≫ (snd (Over.mk x') A).left = _
        rw [← Category.assoc, hΨ, rpt_snd]] at b1
    rw [bv, ← W_eq hβ hβ₀ (e w) (ψp (e w)) (hΨ _) hk hj hi, W, Units.val_mul, map_mul,
      ev_gm _ _ m0 (β₀.s ![kc L (e w₀), j]), ev_inv, ev_gm _ _ m1 (β.s ![kc L (e w₀), i])]
  have hf := (d₀.mono Set.inter_subset_left).mul ((d₁.mono Set.inter_subset_right).inv fun w hw => by
    have m1 : rpt (e w) cpt ∈ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i] := (mem_iff _ _).2 hw.2.2
    show valAt' (rpt (e w)) _ _ ≠ 0
    rw [← ev_gm _ _ m1 (β.s ![kc L (e w₀), i])]
    exact ((Units.isUnit _).map ev).ne_zero)
  have hw : w₀ ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ
        LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left) ![kc L (e w₀), j]} ∩
      {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ rpt (e b) ⁻¹ᵁ LB.wchart L.L (isoφ A Ψ) ![kc L (e w₀), i]} :=
    ⟨⟨trivial, (mem_iff _ _).1 (fiberComplexPoint_mem_thetaTraceChart_of_mem (e w₀) (kc_mem L _) ((mem_iff _ _).2 hw₀.2))⟩,
      ⟨trivial, (mem_iff _ _).1 (fiberComplexPoint_mem_thetaTraceIsoChart_of_comp (e w₀) (ψp (e w₀)) (hΨ _) (kc_mem L _) ((mem_iff _ _).2 hw₀.1))⟩⟩
  exact ((hf.differentiableAt (hN.mem_nhds hw)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hN.mem_nhds hw) key)).differentiableWithinAt

end Hol

section Rig

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x x' : Sp ℂ ⟶ S}
  {Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left} {p : ℕ}
  {β : LB.Gen (isoLB A L Ψ ((p : ℤ) ^ 2))} {β₀ : LB.Gen (isoLB A L (mulT A (Over.mk x) p).left ((p : ℤ) ^ 2))}

theorem val_origin {y y' : Sp ℂ ⟶ S} {Φ : (Over.mk y ⊗ A).left ⟶ (Over.mk y' ⊗ A).left} {k : ℤ}
    {t : LB.Gen (isoLB A L Φ k)} (h : IsRigIso A L Φ k t) {J : (Sp ℂ ⟶ A.left) → L.L.ι} (hJ : Good L.L cpt J) :
    val t (rpt (1 : Over.mk y ⟶ A)) cpt J =
      val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ y) cpt J ^ k *
        val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ y') cpt J ^ (-1 : ℤ) := by
  have e : rpt (1 : Over.mk y ⟶ A) = 𝟙 (Sp ℂ) ≫ (ptSecT A (1 : Over.mk y ⟶ A)).left := (Category.id_comp _).symm
  rw [e]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ h.2.2 (𝟙 _)).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_rigT (Over.mk y) _ (𝟙 _) cpt hJ) (val_rigT (Over.mk y') _ (𝟙 _) cpt hJ))))

theorem rig_ev (y : Sp ℂ ⟶ S) (i : L.L.ι) (h : (y ≫ eSec A) cpt ∈ L.L.U i) :
    ev (gm y cpt ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i))).val =
      valAt' y ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val := by
  have m : y cpt ∈ LB.wchart L.L (fun _ : PUnit => eSec A) (fun _ => i) := Set.mem_iInter.2 fun _ => h
  exact ev_gm y _ m _

theorem rig_trans (y : Sp ℂ ⟶ S) {i i' : L.L.ι} (h : (y ≫ eSec A) cpt ∈ L.L.U i) (h' : (y ≫ eSec A) cpt ∈ L.L.U i') :
    valAt' y ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val =
      valAt' (y ≫ eSec A) (L.L.U i ⊓ L.L.U i') (L.L.g i i').val *
        valAt' y ((L.L.pull (eSec A)).U (fun _ => i')) (L.rig.s (fun _ => i')).val := by
  rw [← rig_ev y i h, ← rig_ev y i' h', ← ev_gm (y ≫ eSec A) (L.L.U i ⊓ L.L.U i') ⟨h, h'⟩, ← map_mul,
    ← Units.val_mul, pullbackGenerator_chart_transition L.rigGen y cpt h h']

theorem bv_rig (hβ : IsRigIso A L Ψ _ β) (hβ₀ : IsRigIso A L (mulT A (Over.mk x) p).left _ β₀)
    (h1 : rpt (1 : Over.mk x ⟶ A) ≫ Ψ = rpt (1 : Over.mk x' ⟶ A)) (i j : L.L.ι)
    (hi : pl (1 : Over.mk x' ⟶ A) cpt ∈ L.L.U i) (hj : pl (1 : Over.mk x ⟶ A) cpt ∈ L.L.U j) :
    valAt' x' ((L.L.pull (eSec A)).U (fun _ => i)) (L.rig.s (fun _ => i)).val =
      bv L β β₀ i j 1 * valAt' x ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val := by
  choose J hJ using fun χ : Sp ℂ ⟶ A.left => exists_chart L.isLB (χ cpt)
  have hG : Good L.L cpt J := hJ
  have hp1 : (1 : Over.mk x ⟶ A) ^ p = 1 := one_pow p
  have r0 := val_origin hβ₀ hG
  have r1 := val_origin hβ hG
  have v0 : val β₀ (rpt (1 : Over.mk x ⟶ A)) cpt J =
      gm (rpt (1 : Over.mk x ⟶ A)) cpt (LB.wchart L.L (isoφ A (mulT A (Over.mk x) p).left)
        ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x ⟶ A))])
        (β₀.s ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x ⟶ A))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd _)
      · show J (rpt _ ≫ (mulT A (Over.mk x) p).left ≫ (snd (Over.mk x) A).left) = _
        rw [← Category.assoc, rpt_mulT, rpt_snd, hp1]; rfl
  have v1 : val β (rpt (1 : Over.mk x ⟶ A)) cpt J =
      gm (rpt (1 : Over.mk x ⟶ A)) cpt (LB.wchart L.L (isoφ A Ψ)
        ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x' ⟶ A))])
        (β.s ![J (pl (1 : Over.mk x ⟶ A)), J (pl (1 : Over.mk x' ⟶ A))]) :=
    val_of _ _ _ _ _ fun k => by
      fin_cases k
      · exact congrArg J (rpt_snd _)
      · show J (rpt _ ≫ Ψ ≫ (snd (Over.mk x') A).left) = _
        rw [← Category.assoc, h1, rpt_snd]; rfl
  have q0 : val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ x) cpt J =
      gm x cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))) := by
    rw [val_of _ _ _ _ (fun _ => J (pl (1 : Over.mk x ⟶ A))) fun _ => by rw [Category.id_comp]; rfl,
      Category.id_comp]
    rfl
  have q1 : val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 (Sp ℂ) ≫ x') cpt J =
      gm x' cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x' ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x' ⟶ A)))) := by
    rw [val_of _ _ _ _ (fun _ => J (pl (1 : Over.mk x' ⟶ A))) fun _ => by rw [Category.id_comp]; rfl,
      Category.id_comp]
    rfl
  have key : W L β β₀ (rpt (1 : Over.mk x ⟶ A)) (J (pl (1 : Over.mk x ⟶ A))) (J (pl (1 : Over.mk x ⟶ A)))
      (J (pl (1 : Over.mk x' ⟶ A))) * gm x cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))) =
      gm x' cpt ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x' ⟶ A))))
        (L.rig.s (fun _ => J (pl (1 : Over.mk x' ⟶ A)))) := by
    rw [W, ← v0, ← v1, r0, r1, q0, q1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  have hj1 : pl ((1 : Over.mk x ⟶ A) ^ p) cpt ∈ L.L.U (J (pl (1 : Over.mk x ⟶ A))) := by rw [hp1]; exact hJ _
  rw [W_eq hβ.2.1 hβ₀.2.1 1 1 h1 (hJ _) hj1 (hJ _)] at key
  have e4 := congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) key
  simp only [Units.val_mul, map_mul] at e4
  rw [rig_ev x _ (hJ (pl (1 : Over.mk x ⟶ A))), rig_ev x' _ (hJ (pl (1 : Over.mk x' ⟶ A)))] at e4
  replace e4 : bv L β β₀ (J (pl (1 : Over.mk x' ⟶ A))) (J (pl (1 : Over.mk x ⟶ A))) 1 * _ = _ := e4
  have e1 := rig_trans x' (i := i) (i' := J (pl (1 : Over.mk x' ⟶ A))) hi (hJ (pl (1 : Over.mk x' ⟶ A)))
  have e2 := rig_trans x (i := j) (i' := J (pl (1 : Over.mk x ⟶ A))) hj (hJ (pl (1 : Over.mk x ⟶ A)))
  have e3 := bv_trans (β := β) (β₀ := β₀) hβ.2.1 hβ₀.2.1 1 1 h1 hi (hJ (pl (1 : Over.mk x' ⟶ A))) (by rw [hp1]; exact hj) hj1
  rw [hp1] at e3
  change bv L β β₀ i j 1 * valAt' (x ≫ eSec A) _ _ = valAt' (x' ≫ eSec A) _ _ * _ at e3
  rw [e1, e2]
  linear_combination (-(valAt' x ((L.L.pull (eSec A)).U (fun _ => J (pl (1 : Over.mk x ⟶ A))))
    (L.rig.s (fun _ => J (pl (1 : Over.mk x ⟶ A)))).val)) * e3 -
    valAt' (x' ≫ eSec A) (L.L.U i ⊓ L.L.U (J (pl (1 : Over.mk x' ⟶ A))))
      (L.L.g i (J (pl (1 : Over.mk x' ⟶ A)))).val * e4

end Rig

theorem hkPtC_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, -, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeValues
end
end

section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeThetaTrace_values_at_complexPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  first | exact @GlobalTheory.HeckeValues.hkPtC_values | exact GlobalTheory.HeckeValues.hkPtC_values | (intros; apply GlobalTheory.HeckeValues.hkPtC_values <;> assumption)
end

section
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add, this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
end
end

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  atlas_forward_decl GlobalTheory.HeckeEx.frame_pull_eq_transition_mul
end

section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section
namespace GlobalTheory.HeckeValueId

theorem core (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (P : Ideal (𝓞 E)) (p i : ℕ)
    (yx zx : Sp ℂ ⟶ Xo.X) (ys : LB.Sec (PPx yx)) (zs : LB.Sec (PPx zx)) (C : Subgroup (Over.mk yx ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom yx ⟶ pullback Xo.univ.t.G.hom zx)
    (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G))
    (cr : Fin (Ideal.absNorm P ^ i) → (Over.mk yx ⟶ Xo.univ.t.G))
    (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ) (t0 : ℂ)
    (hp : p.Prime) (hC2 : ∀ a ∈ C, a ^ p ^ 2 = 1) (hk : IsHkIsog p yx zx C ψ ψp)
    (hr : GlobalTheory.ThetaTrace.IsRepsModTors C p cr)
    (hb0 : ∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0)
    (hbt : ∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a)
    (hbr : ∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (hbh : ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hbv : ∀ (a : Over.mk yx ⟶ Xo.univ.t.G) q (jm : Fin (Ideal.absNorm P ^ i) → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U q →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk zx)) (ψp a)).left ((PPx zx).U (fun _ => q)) (zs.f (fun _ => q)) =
        ∑ m, b q (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk yx)) ((cr m * a) ^ p)).left ((PPx yx).U (fun _ => jm m)) (ys.f (fun _ => jm m)))
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (i₁ i₂ : Fin F.n) (Pm : (F.Di i₁).La →+ (Fin g → ℂ)) (Pm' : (F.Di i₂).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i₁) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm)
    (hP' : IsPeriod (F.Di i₂) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm')
    (hu : yx = F.u i₁ Pm) (hu' : zx = F.u i₂ Pm')
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : Hm.IsHermitian)
    (him : ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di i₁).EF a b)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hn : ∀ j z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (hc : ∀ j j' z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i₁ Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (h0 : ∀ j, ⊤ ≤ (F.ex i₁ Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha : ∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a)))
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx yx),
      pt ≫ Formalism.L2.PjFree.gxFst yx = (F.ex i₁ Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd yx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx yx).U (fun _ => j)) (ys.f (fun _ => j)) = θ z * fr j z)
    (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ)
    (him' : ∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di i₂).EF a b)
    (hd' : ∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hc' : ∀ j j' z, ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex i₂ Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z)
    (h0' : ∀ j, ⊤ ≤ (F.ex i₂ Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha' : ∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a)))
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx zx),
      pt ≫ Formalism.L2.PjFree.gxFst zx = (F.ex i₂ Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd zx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx zx).U (fun _ => j)) (zs.f (fun _ => j)) = t0 * (θ' z * fr' j z)) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
      (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
      (∀ m, ∃ b, h (wm m) = Pm' b) ∧
      ∀ w, ∃ j, ⊤ ≤ (F.ex i₂ Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
        t0 * θ' (h w) * fr' j (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  subst hu hu'
  have hCk : ψp.ker = C := hk.2.2.2.2.2.1
  obtain ⟨gam, h, hg1, hg2, -, hex⟩ := GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo _ g _ F i₁ i₂ Pm Pm' p C
    ψ ψp hP hP' hp hC2 hk
  have eadd := F.ex_add i₁ Pm hP
  have eadd' := F.ex_add i₂ Pm' hP'
  have eker := F.ex_ker i₁ Pm hP
  have eker' := F.ex_ker i₂ Pm' hP'
  have hspan : Submodule.span ℝ (Pm.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  have hsmul : ∀ (d : ℂ) z w, hermForm (d • Hm) z w = d * hermForm Hm z w := fun d z w => by
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ z, M *ᵥ z = h z :=
    ⟨LinearMap.toMatrix' h.toLinearMap, fun z => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hpR : ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w := by
    have key := GlobalTheory.UnitFrameGen.hermForm_eq_of_im _ hspan (((p : ℂ) ^ 2) • Hm) Hm' M (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [hM, hM, ← hg2, ← hg2, him', hg1, hsmul, hpR, Complex.im_ofReal_mul, him]
      push_cast; ring)
    intro z w
    rw [← hM, ← hM, key, hsmul]
  have hpow : ∀ (m : ℕ) w, F.ex i₁ Pm (m • w) = F.ex i₁ Pm w ^ m := fun m w => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact (eker 0).2 ⟨0, map_zero Pm⟩
    | succ m ih => rw [succ_nsmul, eadd, ih, pow_succ]
  have hL : ∀ a ∈ Pm.range, h a ∈ Pm'.range := by
    rintro _ ⟨a, rfl⟩; exact ⟨gam a, hg2 a⟩
  have hhol := GlobalTheory.ClassUniq.isHolTo_ex F i₁ Pm hP
  have hhol' := GlobalTheory.ClassUniq.isHolTo_ex F i₂ Pm' hP'
  have hfr := GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul E H Dw l Xo (F.u i₁ Pm) (F.u i₂ Pm') p ψp b g Pm.range Pm'.range (F.ex i₁ Pm)
    (F.ex i₂ Pm') h hspan hhol hhol' eadd (fun a ha => (eker a).2 ha) hex hL hb0 hbt hbr (hbh g _ hhol) Hm χl fr hH
    hd hn hc h0 (by rintro _ ⟨a, rfl⟩ j z; exact ha a j z) Hm' χl' fr' hHH hd' hc' h0'
    (by rintro _ ⟨a, rfl⟩ j z; exact ha' a j z)
  choose wm hwm using fun m => F.ex_onto i₁ Pm hP (cr m)
  have hwmΛ : ∀ m, ∃ b', h (wm m) = Pm' b' := fun m => by
    have e1 : F.ex i₂ Pm' (h (wm m)) = 1 := by
      rw [hex, hwm, ← MonoidHom.mem_ker, hCk]; exact hr.1 m
    obtain ⟨b', hb'⟩ := (eker' _).1 e1
    exact ⟨b', hb'.symm⟩
  refine ⟨h, wm, fun a => ⟨gam a, (hg2 a).symm⟩, hHH, hwmΛ, fun w => ?_⟩
  obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex i₂ Pm' (h w)).left
  refine ⟨j, hj, ?_⟩
  have hjz : ⊤ ≤ (ψp (F.ex i₁ Pm w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [← hex]; exact hj
  choose jm hjm using fun m => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((cr m * F.ex i₁ Pm w) ^ p).left
  have hsum := hbv (F.ex i₁ Pm w) j jm hjz hjm
  have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  rw [← hex] at hsum e1 e2
  rw [hv' j (h w) _ e1 e2 hj] at hsum
  rw [_root_.mul_assoc, hsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hq : cr m * F.ex i₁ Pm w = F.ex i₁ Pm (w + wm m) := by rw [← hwm, ← eadd, add_comm]
  have hpw : F.ex i₁ Pm (w + wm m) ^ p = F.ex i₁ Pm ((p : ℂ) • (w + wm m)) := by
    rw [Nat.cast_smul_eq_nsmul, hpow]
  have hjm' := hjm m
  rw [hq, hpw] at hjm' ⊢
  have f1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  have f2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  rw [hv (jm m) _ _ f1 f2 hjm']
  obtain ⟨b', hb'⟩ := hwmΛ m
  have hjw : ⊤ ≤ (F.ex i₂ Pm' (h (w + wm m))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [map_add, eadd', hb', (eker' _).2 ⟨b', rfl⟩, _root_.mul_one]; exact hj
  have hf := hfr (w + wm m) j (jm m) hjw hjm'
  rw [map_add] at hf
  rw [hf]; ring

theorem hecke_theta_value_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
    (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
    (∀ m, ∃ b, h (wm m) = Pm' b) ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h w) * fr' j (h w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ P p i k k' x x' C z t hA hK hz hb g e F ik Pm Pm' hP hP' hu hu'
    Hm χl fr θ hH _ him hd hn hc h0 ha hv Hm' χl' fr' θ' _ _ him' hd' _ hc' h0' ha' hv'
  obtain ⟨ψ, ψp, n, cr, b, hk, hr, hb0, hbt, hbr, hbh, hbv⟩ := GlobalTheory.T.heckeThetaTrace_values_at_complexPoints E H Dw l Xo c σ p (U.un k x) z C hz
  have hcard : n = Ideal.absNorm P ^ i := by
    letI := fieldCAt σ
    haveI := algClosedCAt σ
    exact GlobalTheory.ThetaTrace.card_reps hA.2.2.1.pos hK hr
  subst hcard
  obtain ⟨hzx, -, hbc⟩ := hb
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x z.x
      (U.un k' x').s z.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hv'' : ∀ j w (pt : Sp ℂ ⟶ Gx z.x), pt ≫ Formalism.L2.PjFree.gxFst z.x = (F.ex (ik k') Pm' w).left →
      pt ≫ Formalism.L2.PjFree.gxSnd z.x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex (ik k') Pm' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' w * fr' j w) := by
    intro j w pt e1 e2 hj
    have hw0' : (F.ex (ik k') Pm' w).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) :=
      (Over.w (F.ex (ik k') Pm' w)).trans hu'.symm
    exact GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hzx _ _ _ hbc'
      (Over.homMk (F.ex (ik k') Pm' w).left hw0') j _ _
      (fun pt' h1 h2 => hv' j w pt' h1 h2 hj)
      (fun pt' h1 h2 => by
        obtain rfl : pt' = pt := Limits.pullback.hom_ext (h2.trans e2.symm) (h1.trans e1.symm)
        rfl)
  exact core E H Dw l Xo c σ P p i (U.un k x).x z.x (U.un k x).s z.s C ψ ψp cr b _ hA.2.2.1
    (fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha) hk hr hb0 hbt hbr hbh hbv g e F (ik k) (ik k') Pm Pm' hP hP'
    hu (hzx.trans hu') Hm χl fr θ hH him hd hn hc h0 ha hv Hm' χl' fr' θ' him' hd' hc' (by rw [hzx]; exact h0') ha' hv''

end GlobalTheory.HeckeValueId
end
end
