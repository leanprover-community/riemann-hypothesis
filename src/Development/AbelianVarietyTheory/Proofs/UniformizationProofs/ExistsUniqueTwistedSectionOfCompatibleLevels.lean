module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLimit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecLimit

section Twist

variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)

abbrev twφ (T : Over (Spec (CommRingCat.of V))) : Fin 2 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (translPt D.P.A (toUnit T ≫ D.c α)).left]

abbrev ptφ : Fin 2 → (Spec (CommRingCat.of V) ⟶ D.P.A.left) := ![(D.c α).left, (η[D.P.A]).left]

abbrev famVals {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) : Set (Vals D.P.L Y) :=
  secVals D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε k)

variable {D k α}

theorem mul_mem_famVals (u : LB.Gen (LB.LinComb D.P.L (ptφ D α) ![-1, 1])) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of V))) {Y : Scheme.{0}} (h : Y ⟶ (T ⊗ D.P.A).left) {π : Y ⟶ D.P.A.left}
    (hπ : h ≫ (snd T D.P.A).left = π) (w : Vals D.P.L Y) :
    w * evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)) ∈ famVals D k α π ↔
      w ∈ secVals D.P.L (fun j => h ≫ twφ D α T j) ![(k : ℤ) - 1, 1] := by
  have hZ : h ≫ (T ⊗ D.P.A).hom = π ≫ D.P.A.hom := by
    rw [← Over.w (snd T D.P.A), ← Category.assoc, hπ]
  let Z : Over (Spec (CommRingCat.of V)) := Over.mk (π ≫ D.P.A.hom)
  let hO : Z ⟶ T ⊗ D.P.A := Over.homMk h hZ
  let πO : Z ⟶ D.P.A := Over.homMk π rfl
  have h1 : hO ≫ snd T D.P.A = πO := Over.OverMorphism.ext hπ
  have e1 : hO ≫ translPt D.P.A (toUnit T ≫ D.c α) = πO ≫ padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α) := by
    unfold translPt padd
    simp only [comp_lift_assoc, comp_toUnit_assoc, h1, Category.comp_id]
    exact mul_comm (toUnit Z ≫ D.c α) πO
  have hmor : h ≫ (translPt D.P.A (toUnit T ≫ D.c α)).left =
      π ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α)).left := by
    exact congrArg Over.Hom.left e1
  refine mul_mem_iff (φ := fun j => h ≫ twφ D α T j)
    (ε := ![(k : ℤ) - 1, 1]) (φ' := fun i => π ≫ D.famφB α i) (ε' := DegPre.famε k)
    D.P.isLB _ (DVR.pullGen_isGen _ _ _ u hu _) ?_ w
  intro U _ g
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Fin.prod_univ_four, twφ, ptφ, DegPre.famφB, DegPre.famε, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, hmor, hπ, Category.comp_id,
    zpow_one, Over.comp_left, Over.toUnit_left, Category.assoc]
  exact (@mul_assoc U _ _ _ _).symm

theorem isPullback_snd (T : Over (Spec (CommRingCat.of V))) :
    IsPullback (snd T D.P.A).left (fst T D.P.A).left D.P.A.hom T.hom := by
  rw [Over.snd_left, Over.fst_left]
  exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip


private theorem exists_isBas_famVals_of_isPullback [IsLocalRing V] (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := by
  obtain ⟨b0, hb0⟩ := (hT _ D.P k hk R t (toUnit (Over.mk t) ≫ D.c α)).1
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  let e := H.flip.isoPullback
  have hπ : e.hom ≫ (snd (Over.mk t) D.P.A).left = π := H.flip.isoPullback_hom_snd
  have hf : e.hom ≫ (fst (Over.mk t) D.P.A).left = f := H.flip.isoPullback_hom_fst
  let E := Scheme.ΓSpecIso (CommRingCat.of R)
  let p := (fst (Over.mk t) D.P.A).left.appTop.hom
  let gR : R →+* Γ((Over.mk t ⊗ D.P.A).left, ⊤) := p.comp E.inv.hom
  have hgR (x : Γ(Spec (CommRingCat.of R), ⊤)) : gR (E.hom.hom x) = p x :=
    congrArg p (Iso.hom_inv_id_apply E x)
  have hb1 : IsBas (cst D.P.L (fst (Over.mk t) D.P.A).left)
      (secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1])
      (fun i => ev (b0 i)) := by
    refine isBas_of_comb D.P.isLB gR b0 (fun s => ?_)
    obtain ⟨r, hr, hru⟩ := hb0 s
    refine ⟨fun i => E.hom.hom (r i), fun j => ?_, fun a ha => ?_⟩
    · rw [hr j]
      simp only [hgR]
      rfl
    · have h2 := hru (fun i => E.inv.hom (a i)) ha
      funext i
      exact (Iso.inv_hom_id_apply E (a i)).symm.trans (congrArg E.hom.hom (congrFun h2 i))
  let uπ : (Vals D.P.L Y)ˣ := evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom))
  have key := fun w => mul_mem_famVals (k := k) u hu (Over.mk t) e.hom hπ w
  have hinj : Function.Injective (pull D.P.L e.hom) :=
    Function.LeftInverse.injective (g := pull D.P.L e.inv) (fun w => by rw [pull_pull, Iso.inv_hom_id, pull_id])
  have hS : ∀ s', s' ∈ famVals D k α π ↔
      ∃ s ∈ secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1],
        s' = pull D.P.L e.hom s * (uπ : Vals D.P.L Y) := by
    intro s'
    constructor
    · intro hs'
      let w : Vals D.P.L Y := s' * ↑uπ⁻¹
      have hw : w * (uπ : Vals D.P.L Y) ∈ famVals D k α π :=
        (Units.inv_mul_cancel_right s' uπ).symm ▸ hs'
      refine ⟨pull D.P.L e.inv w, pull_mem ((key w).1 hw) e.inv (fun j => ?_), ?_⟩
      · simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      change s' = pull D.P.L e.hom (pull D.P.L e.inv (s' * ↑uπ⁻¹)) * ↑uπ
      rw [pull_pull, Iso.hom_inv_id, pull_id, Units.inv_mul_cancel_right]
    · rintro ⟨s, hs, rfl⟩
      exact (key _).2 (pull_mem hs e.hom (fun j => rfl))
  have hf' : e.hom ≫ (fst (Over.mk t) D.P.A).left =
      f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using hf
  have hscalar (a : R) : pull D.P.L e.hom (cst D.P.L (fst (Over.mk t) D.P.A).left a) =
      cst D.P.L f a :=
    pull_cst (L := D.P.L) (RingHom.id R) hf' a
  exact ⟨fun i => pull D.P.L e.hom (ev (b0 i)) * ↑uπ,
    IsBas.transfer (ρ := pull D.P.L e.hom) hscalar hinj uπ hS hb1⟩

variable [IsLocalRing V]

theorem exists_isBas (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := exists_isBas_famVals_of_isPullback hT hk H

abbrev resPt (V : Type) [CommRing V] [IsLocalRing V] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _)

theorem exists_lift (hT : SecTwistSt) (hk : 1 ≤ k) (w : Vals D.P.L (resPt V ⊗ D.P.A).left)
    (hw : w ∈ famVals D k α (snd (resPt V) D.P.A).left) :
    ∃ s ∈ famVals D k α (𝟙 _), w = pull D.P.L (snd (resPt V) D.P.A).left s := by
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  have keyX := fun v => mul_mem_famVals (k := k) u hu (resPt V) (𝟙 _) (π := (snd (resPt V) D.P.A).left)
    (Category.id_comp _) v
  have hw1 := (keyX (w * ↑(evU (LB.pullGen D.P.L _ _ u ((snd (resPt V) D.P.A).left ≫ D.P.A.hom)))⁻¹)).1
    (by rw [Units.inv_mul_cancel_right]; exact hw)
  let whisk : resPt V ⊗ D.P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A :=
    Over.homMk (V := Over.mk (𝟙 (Spec (CommRingCat.of V)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
      rfl ▷ D.P.A
  have ht0 : whisk ≫ snd _ D.P.A = snd (resPt V) D.P.A := whiskerRight_snd _ _
  have ht1 : whisk ≫ translPt D.P.A (toUnit _ ≫ D.c α) = translPt D.P.A (toUnit (resPt V) ≫ D.c α) := by
    simp only [whisk, translPt, comp_lift_assoc, whiskerRight_snd, comp_toUnit_assoc]
  have hφ : (fun j => 𝟙 _ ≫ twφ D α (resPt V) j) = fun j => whisk.left ≫
      ![(snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left,
        (translPt D.P.A (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of V)))) ≫ D.c α)).left] j := by
    funext j
    match j with
    | 0 =>
      simp only [twφ, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht0]
    | 1 =>
      simp only [twφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht1]
  rw [hφ] at hw1
  obtain ⟨sbar, hsbar⟩ := hw1
  obtain ⟨s, hs⟩ := (hT _ D.P k hk V (𝟙 _) (toUnit _ ≫ D.c α)).2 sbar
  have hps : sbar = DVR.pullSec D.P.L _ _ s whisk.left := DVR.SecOps.sec_ext (fun j => hs j)
  have hev : ev sbar = pull D.P.L whisk.left (ev s) := by
    rw [hps]
    exact ev_pullSec _ _
  let i : D.P.A.left ⟶ (Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A).left :=
    pullback.lift D.P.A.hom (𝟙 _) (by simp)
  have hi : i ≫ (snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left = 𝟙 _ := pullback.lift_snd _ _ _
  have key0 := fun v => mul_mem_famVals (k := k) u hu (Over.mk (𝟙 (Spec (CommRingCat.of V)))) i hi v
  refine ⟨pull D.P.L i (ev s) * ↑(evU (LB.pullGen D.P.L _ _ u (𝟙 _ ≫ D.P.A.hom))),
    (key0 _).2 (pull_mem ⟨s, rfl⟩ i (fun j => rfl)), ?_⟩
  have hc := pullback.condition (f := (resPt V).hom) (g := D.P.A.hom)
  have hsi : (snd (resPt V) D.P.A).left ≫ i = whisk.left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, i, pullback.lift_fst, whisk, Over.whiskerRight_left_fst]
      simpa using hc.symm
    · simp only [Category.assoc, i, pullback.lift_snd, Category.comp_id, whisk, Over.whiskerRight_left_snd]
      rfl
  rw [map_mul, pull_pull, hsi, ← hev, hsbar, pull_evU, pull_pull, Category.id_comp, ← pull_evU,
    Units.inv_mul_cancel_right]

theorem isBas_thick (hT : SecTwistSt) (hk : 1 ≤ k) {b : Fin (k ^ D.P.g) → Vals D.P.L D.P.A.left}
    (hb : IsBas (cst D.P.L D.P.A.hom) (famVals D k α (𝟙 _)) b) (e : ℕ) :
    IsBas (cst D.P.L (pullback.snd D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (famVals D k α (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (fun i => pull D.P.L (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)) (b i)) := by
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hI : IsLocalRing.maximalIdeal V ^ (e + 1) ≤ IsLocalRing.maximalIdeal V :=
    Ideal.pow_le_self (Nat.succ_ne_zero e)
  let g' : V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.factor hI
  have : IsLocalHom g' := IsLocalHom.of_surjective g' (Ideal.Quotient.factor_surjective hI)
  have hg' : g'.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (e + 1))) =
      IsLocalRing.residue V := Ideal.Quotient.factor_comp_mk hI
  have hfactor : Spec.map (CommRingCat.ofHom g') ≫ thick V (IsLocalRing.maximalIdeal V) e =
      (resPt V).hom := by
    change Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  have H := IsPullback.of_hasPullback D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)
  have H' := isPullback_snd (D := D) (resPt V)
  have hm : (snd (resPt V) D.P.A).left ≫ D.P.A.hom =
      ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) ≫
        thick V (IsLocalRing.maximalIdeal V) e :=
    H'.w.trans ((congrArg (fun t => (fst (resPt V) D.P.A).left ≫ t) hfactor.symm).trans
      (Category.assoc _ _ _).symm)
  let m := pullback.lift (snd (resPt V) D.P.A).left
    ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) hm
  obtain ⟨b', hb'⟩ := exists_isBas (α := α) hT hk H
  obtain ⟨b'', hb''⟩ := exists_isBas (α := α) hT hk H'
  refine IsBas.reduce (ρ' := pull D.P.L m) (g' := g') (fun a => pull_cst _ H.w a)
    (fun a => pull_cst g' (pullback.lift_snd _ _ _) a) ?_ ?_ ?_ hb hb' hb''
  · intro s hs
    exact pull_mem hs _ (fun i => congrArg (fun f => pullback.fst _ _ ≫ f)
      (Category.id_comp (D.famφB α i)).symm)
  · intro s hs
    exact pull_mem hs m (fun i => (pullback.lift_fst_assoc _ _ _ _).symm)
  · intro s hs
    obtain ⟨s0, hs0, h⟩ := exists_lift hT hk s hs
    exact ⟨s0, hs0, h.trans ((pull_pull _ m s0).trans
      (congrArg (fun q => pull D.P.L q s0) (pullback.lift_fst _ _ _))).symm⟩

private theorem existsUnique_of_range {A W : Type*} {ev : A → W} {P : W → Prop}
    (hinj : Function.Injective ev) (h : ∃! w, w ∈ Set.range ev ∧ P w) :
    ∃! a, P (ev a) := by
  obtain ⟨w, ⟨⟨a, ha⟩, hw⟩, hu⟩ := h
  exact ⟨a, Eq.mp (congrArg P ha.symm) hw, fun a' ha' =>
    hinj ((hu (ev a') ⟨⟨a', rfl⟩, ha'⟩).trans ha.symm)⟩

private theorem pull_ev_eq_iff {X B Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K : Type} [Fintype K] {φ : K → (B ⟶ X)} {ψ : K → (Y ⟶ X)} {ε : K → ℤ}
    {p : Y ⟶ B} (hp : ∀ i, ψ i = p ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L ψ ε)) :
    pull L p (ev s) = ev t ↔ ∀ z J, Good L z J → sval s p z J = sval t (𝟙 Y) z J := by
  have hid z (J : {J // Good L z J}) :
      (pull L p (ev s)) Y (𝟙 Y) z J = sval s p z J.1 :=
    congrArg (fun r => sval s r z J.1) (Category.id_comp p)
  refine ⟨fun h z J hJ => (hid z ⟨J, hJ⟩).symm.trans
    (congrArg (fun w : Vals L Y => w Y (𝟙 Y) z ⟨J, hJ⟩) h), fun h => ?_⟩
  have hs : pull L p (ev s) ∈ secVals L ψ ε :=
    pull_mem (⟨s, rfl⟩ : ev s ∈ secVals L φ ε) p hp
  exact secVals_ext hL hs ⟨t, rfl⟩ fun z J => (hid z J).trans (h z J.1 J.2)

private theorem existsUnique_sec_of_isBas_lemma {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := by
  have hφ : (fun i => 𝟙 B ≫ φ i) = φ := funext fun i => Category.id_comp (φ i)
  have hb₀ : IsBas (cst L p) (secVals L φ ε) b := hφ ▸ hb
  have hmem : ∀ e, ev (f e) ∈ secVals L (fun i => π e ≫ φ i) ε := fun e => ⟨f e, rfl⟩
  have hc (e : ℕ) : pull L (θ e) (ev (f (e + 1))) = ev (f e) :=
    (pull_ev_eq_iff hL (fun i => (congrArg (fun r => r ≫ φ i) (hθ e)).symm.trans
      (Category.assoc (θ e) (π (e + 1)) (φ i))) (f (e + 1)) (f e)).2 (hf e)
  have hlim : ∃! w : Vals L B, w ∈ secVals L φ ε ∧ ∀ e, pull L (π e) w = ev (f e) :=
    existsUnique_limit I (W := Vals L B) (T := fun e => Vals L (Y e)) (c := cst L p)
    (c' := fun e => cst L (q e)) (ρ := fun e => pull L (π e)) (τ := fun e => pull L (θ e))
    (fun e => pull_cst (L := L) (Ideal.Quotient.mk (I ^ (e + 1))) (hq e))
    (fun e w => (pull_pull (π (e + 1)) (θ e) w).trans (congrArg (fun r => pull L r w) (hθ e)))
    (S := secVals L φ ε) (S' := fun e => secVals L (fun i => π e ≫ φ i) ε)
    (fun z => comb_mem (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) z hb₀.1) hb₀ hb'
    (fun e => ev (f e)) hmem hc
  have hevinj : Function.Injective (ev (L := L) (φ := φ) (ε := ε)) :=
    fun s t h => eq_of_val hL fun z J => congrArg (fun w : Vals L B => w B (𝟙 B) z J) h
  refine (existsUnique_congr (fun s => ?_)).1 (existsUnique_of_range hevinj hlim)
  exact forall_congr' (fun e => pull_ev_eq_iff hL (fun i => rfl) s (f e))

end Twist

theorem existsUnique_sec_of_isBas {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := existsUnique_sec_of_isBas_lemma hL I hθ hq hb hb' f hf

theorem existsUnique_sec_of_compatible : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  intro _ hL2 V _ _ _ hV D k hk α f hf
  have hT : SecTwistSt := hL2.secTwist
  have : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  obtain ⟨b, hb⟩ := exists_isBas (α := α) (R := V) (t := 𝟙 _) hT hk
    (IsPullback.of_id_fst (f := D.P.A.hom))
  exact existsUnique_sec_of_isBas D.P.isLB (IsLocalRing.maximalIdeal V) (p := D.P.A.hom)
    (π := fun e => (D.prBe (IsLocalRing.maximalIdeal V) e).left)
    (q := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e D.P.A).hom)
    (θ := fun e => thickMap V (IsLocalRing.maximalIdeal V) e D.P.A)
    (fun e => by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ = pullback.fst _ _
      rw [pullback.lift_fst, Category.comp_id]) (fun e => pullback.condition) hb
    (fun e => isBas_thick hT hk hb e) f hf

end GlobalTheory.SecLimit
