import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoincareDeRhamDuality.DeRhamPerfectPairing.H1OnPointsEqZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {X Y Y' : Scheme.{0}}

abbrev Inn {B : Type} [CommRing B] (y : Sp B ⟶ Y) (U : Y.Opens) : Prop := ⊤ ≤ y ⁻¹ᵁ U

section
variable {B B' : Type} [CommRing B] [CommRing B'] {y : Sp B ⟶ Y} {U V : Y.Opens}

theorem Inn.map (h : Inn y U) (ρ : B →+* B') : Inn (spMap ρ ≫ y) U :=
  fun p _ ↦ h (Set.mem_univ ((spMap ρ) p))

theorem Inn.mono (h : Inn y U) (e : U ≤ V) : Inn y V := fun _ hp ↦ e (h hp)

theorem Inn.inf (h : Inn y U) (h' : Inn y V) : Inn y (U ⊓ V) := fun _ hp ↦ ⟨h hp, h' hp⟩

theorem valR_resU (e : V ≤ U) (h : Inn y V) (f : Γ(Y, U)ˣ) : valR y V (res e f).val = valR y U f.val :=
  valR_res y e h f.val

theorem valR_inv_mul (h : Inn y U) (f : Γ(Y, U)ˣ) : valR y U (f⁻¹).val * valR y U f.val = 1 := by
  rw [← valR_mul _ _ h, Units.inv_mul, valR_one _ _ h]

end

def zs (Y : Scheme.{0}) : Y ⟶ Sp ℤ := specZIsTerminal.from Y

@[reducible] def zPt (B : Type) [CommRing B] (y : Sp B ⟶ Y) : Pt (zs Y) where
  B := B
  x := y
  w := specZIsTerminal.hom_ext _ _

theorem exists_sec_cover {J : Type} (W : J → Y.Opens) (U : Y.Opens) (h1 : ∀ j, W j ≤ U) (h2 : U ≤ ⨆ j, W j)
    (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B)
    (hF : ∀ (j : J) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (W j) →
      F B' (spMap ρ ≫ y) = ρ (F B y)) :
    ∃ f : Γ(Y, U), ∀ (j : J) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (W j) → F B y = valR y U f := by
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover ℤ Y (zs Y) J W U h1 h2 (fun P ↦ F P.B P.x) fun j P Q φ hP ↦ by
    have := hF j P.B Q.B (φ.ρ : P.B →+* Q.B) P.x hP
    rw [φ.pt] at this
    exact this
  exact ⟨f, fun j B _ y h ↦ hf j (zPt B y) h⟩

theorem sec_ext_cover {J : Type} (W : J → Y.Opens) (hW : ⨆ j, W j = ⊤) (V : Y.Opens) (f g : Γ(Y, V))
    (H : ∀ (j : J) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y V → Inn y (W j) → valR y V f = valR y V g) :
    f = g :=
  eq_of_valR_eq_on_cover (zs Y) W hW V f g fun P j h h' ↦ H j P.B P.x h h'

theorem sec_ext (V : Y.Opens) (f g : Γ(Y, V))
    (H : ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y V → valR y V f = valR y V g) : f = g :=
  sec_ext_cover (fun _ : Unit ↦ ⊤) (by simp) V f g fun _ B _ y h _ ↦ H B y h

theorem exists_sec (U : Y.Opens) (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B)
    (hF : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y U →
      F B' (spMap ρ ≫ y) = ρ (F B y)) :
    ∃ f : Γ(Y, U), ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y U → F B y = valR y U f := by
  obtain ⟨f, hf⟩ := exists_sec_cover (fun _ : Unit ↦ U) U (fun _ ↦ le_rfl) (by simp) F fun _ ↦ hF
  exact ⟨f, hf ()⟩

theorem exists_unit (U : Y.Opens) (F : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (hF : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y U →
      (F B' (spMap ρ ≫ y)).val = ρ (F B y).val) :
    ∃ f : Γ(Y, U)ˣ, ∀ (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y U → (F B y).val = valR y U f.val := by
  obtain ⟨a, ha⟩ := exists_sec U (fun B _ y ↦ (F B y).val) hF
  obtain ⟨b, hb⟩ := exists_sec U (fun B _ y ↦ ((F B y)⁻¹).val) fun B B' _ _ ρ y h ↦ by
    have e1 := hF B B' ρ y h
    have e2 : ((F B' (spMap ρ ≫ y))⁻¹).val * (F B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have e3 : ρ ((F B y)⁻¹).val * ρ (F B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    change ((F B' (spMap ρ ≫ y))⁻¹).val = ρ ((F B y)⁻¹).val
    rw [e1] at e2
    linear_combination ρ ((F B y)⁻¹).val * e2 - ((F B' (spMap ρ ≫ y))⁻¹).val * e3
  have hab : a * b = 1 := sec_ext U _ _ fun B _ y h ↦ by
    rw [valR_mul _ _ h, valR_one _ _ h, ← ha B y h, ← hb B y h]
    exact Units.mul_inv _
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, ha⟩

abbrev Kap (Y : Scheme.{0}) : Type 1 :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (_ : B →+* B') (_ : Sp B ⟶ Y), B'

def Rel (N : LB Y) (κ : Kap Y) : Prop :=
  ∃ w : N.ι → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ,
    (∀ (i j : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → Inn y (N.U j) →
      (w i B y).val = valR y (N.U i ⊓ N.U j) (N.g i j).val * (w j B y).val) ∧
    ∀ (i : N.ι) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (N.U i) →
      (w i B' (spMap ρ ≫ y)).val = ρ (w i B y).val * κ B B' ρ y

variable {N N' : LB Y} {κ κ' κ'' : Kap Y}

theorem Rel.twist (h : Rel N κ) (u : ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ' B B' ρ y * ρ (u B y).val = κ B B' ρ y * (u B' (spMap ρ ≫ y)).val) : Rel N κ' := by
  obtain ⟨w, h1, h2⟩ := h
  refine ⟨fun i B _ y ↦ w i B y * u B y, fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · simp only [Units.val_mul]
    rw [h1 i j B y hi hj, mul_assoc]
  · simp only [Units.val_mul, map_mul]
    rw [h2 i B B' ρ y hi]
    linear_combination -ρ (w i B y).val * e B B' ρ y

theorem Rel.congr (h : Rel N κ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), κ' B B' ρ y = κ B B' ρ y) :
    Rel N κ' :=
  h.twist (fun _ _ _ ↦ 1) fun B B' _ _ ρ y ↦ by rw [e, Units.val_one, Units.val_one, map_one]

theorem Rel.triv (h : Rel N κ)
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), κ B B' ρ y = 1) :
    ∃ t : LB.Gen N, t.IsGen := by
  obtain ⟨w, h1, h2⟩ := h
  choose t ht using fun i ↦ exists_unit (N.U i) (w i) fun B B' _ _ ρ y hi ↦ by
    rw [h2 i B B' ρ y hi, e, mul_one]
  refine ⟨⟨t⟩, fun i j ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_)⟩
  have hi := hy.mono inf_le_left
  have hj := hy.mono inf_le_right
  rw [Units.val_mul, valR_mul _ _ hy, valR_resU _ hy, valR_resU _ hy]
  exact (ht i B y hi).symm.trans ((h1 i j B y hi hj).trans (congrArg _ (ht j B y hj)))

theorem Rel.div (h : Rel N κ) (h' : Rel N' κ')
    (e : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y),
      κ'' B B' ρ y * κ' B B' ρ y = κ B B' ρ y) : Rel (LB.div N N') κ'' := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨w', h1', h2'⟩ := h'
  refine ⟨fun p B _ y ↦ w p.1 B y * (w' p.2 B y)⁻¹, fun p q B _ y hp hq ↦ ?_, fun p B B' _ _ ρ y hp ↦ ?_⟩
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have hq' : Inn y (N.U q.1 ⊓ N'.U q.2) := hq
    have hy : Inn y (N.U p.1 ⊓ N'.U p.2 ⊓ (N.U q.1 ⊓ N'.U q.2)) := hp'.inf hq'
    have a1 := h1 p.1 q.1 B y (hp'.mono inf_le_left) (hq'.mono inf_le_left)
    have a2 := h1' p.2 q.2 B y (hp'.mono inf_le_right) (hq'.mono inf_le_right)
    have a3 := valR_inv_mul ((hp'.mono inf_le_right).inf (hq'.mono inf_le_right)) (N'.g p.2 q.2)
    have a4 : ((w' p.2 B y)⁻¹).val * (w' p.2 B y).val = 1 := Units.inv_mul _
    have a5 : ((w' q.2 B y)⁻¹).val * (w' q.2 B y).val = 1 := Units.inv_mul _
    have a6 : valR y ((LB.div N N').U p ⊓ (LB.div N N').U q) ((LB.div N N').g p q).val =
        valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val * valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val := by
      refine (valR_mul y _ hy _ _).trans (congrArg₂ (· * ·) (valR_resU _ hy _) ?_)
      exact valR_resU (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hy
        (N'.g p.2 q.2)⁻¹
    rw [a6]
    simp only [Units.val_mul]
    rw [a2] at a4
    rw [a1]
    generalize valR y (N.U p.1 ⊓ N.U q.1) (N.g p.1 q.1).val = G at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) ((N'.g p.2 q.2)⁻¹).val = Gi at *
    generalize valR y (N'.U p.2 ⊓ N'.U q.2) (N'.g p.2 q.2).val = G' at *
    generalize ((w' p.2 B y)⁻¹).val = a at *
    generalize ((w' q.2 B y)⁻¹).val = b at *
    generalize (w' q.2 B y).val = c at *
    generalize (w q.1 B y).val = d at *
    have k : a = Gi * b := by linear_combination (-a * b * c) * a3 - a * a5 + Gi * b * a4
    rw [k]; ring
  · have hp' : Inn y (N.U p.1 ⊓ N'.U p.2) := hp
    have a1 := h2 p.1 B B' ρ y (hp'.mono inf_le_left)
    have a2 := h2' p.2 B B' ρ y (hp'.mono inf_le_right)
    have a4 : ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val * (w' p.2 B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have a5 : ρ ((w' p.2 B y)⁻¹).val * ρ (w' p.2 B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [Units.val_mul, map_mul]
    rw [a2] at a4
    rw [a1, ← e]
    generalize ((w' p.2 B' (spMap ρ ≫ y))⁻¹).val = a' at *
    generalize ρ ((w' p.2 B y)⁻¹).val = a at *
    generalize ρ (w' p.2 B y).val = c at *
    have k : a' * κ' B B' ρ y = a := by linear_combination a * a4 - a' * κ' B B' ρ y * a5
    rw [← k]; ring

theorem Rel.cls_eq (hN : N.IsLB) (hN' : N'.IsLB) (h : Rel N κ) (h' : Rel N' κ) : cls N hN = cls N' hN' := by
  have := (cls_eq_zero_iff (LB.isLB_div hN hN')).2
    ((h.div (κ'' := fun _ _ _ _ _ _ ↦ 1) h' fun _ _ _ _ _ _ ↦ one_mul _).triv fun _ _ _ _ _ _ ↦ rfl)
  rwa [cls_div hN hN', sub_eq_zero] at this

theorem Rel.pull (h : Rel N κ) (ψ : Y' ⟶ Y) : Rel (N.pull ψ) fun B B' _ _ ρ y ↦ κ B B' ρ (y ≫ ψ) := by
  obtain ⟨w, h1, h2⟩ := h
  have hin : ∀ (j : PUnit → N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y'), Inn y ((N.pull ψ).U j) →
      Inn (y ≫ ψ) (N.U (j PUnit.unit)) := fun j B _ y h p _ ↦
    LB.wchart_le N (K := PUnit) (fun _ ↦ ψ) j PUnit.unit (h (Set.mem_univ p))
  refine ⟨fun j B _ y ↦ w (j PUnit.unit) B (y ≫ ψ), fun i j B _ y hi hj ↦ ?_, fun i B B' _ _ ρ y hi ↦ ?_⟩
  · refine (h1 _ _ B _ (hin i B y hi) (hin j B y hj)).trans (congrArg (· * _) ?_)
    have a := (hin i B y hi).inf (hin j B y hj)
    have b := hi.inf hj
    exact (valR_eq _ _ a _).trans ((GlobalTheory.DeRham.evalAt_pull_g N ψ y i j a b).trans (valR_eq y _ b _).symm)
  · have := h2 _ B B' ρ _ (hin i B y hi)
    rw [← Category.assoc] at this
    exact this

theorem exists_rel {I : Type} (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤) (κ : Kap Y)
    (w : I → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → Bˣ)
    (h2 : ∀ (i : I) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (U i) →
      (w i B' (spMap ρ ≫ y)).val = ρ (w i B y).val * κ B B' ρ y) :
    ∃ g : ∀ i j, Γ(Y, U i ⊓ U j)ˣ, LB.IsLB ⟨I, U, g⟩ ∧ Rel ⟨I, U, g⟩ κ := by
  choose g hg using fun i j ↦ exists_unit (U i ⊓ U j) (fun B _ y ↦ w i B y * (w j B y)⁻¹) fun B B' _ _ ρ y h ↦ by
    have a1 := h2 i B B' ρ y (h.mono inf_le_left)
    have a2 := h2 j B B' ρ y (h.mono inf_le_right)
    have a4 : ((w j B' (spMap ρ ≫ y))⁻¹).val * (w j B' (spMap ρ ≫ y)).val = 1 := Units.inv_mul _
    have a5 : ρ ((w j B y)⁻¹).val * ρ (w j B y).val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    simp only [Units.val_mul, map_mul]
    rw [a2] at a4
    rw [a1]
    generalize ((w j B' (spMap ρ ≫ y))⁻¹).val = a' at *
    generalize ρ ((w j B y)⁻¹).val = a at *
    generalize ρ (w j B y).val = c at *
    have k : a' * κ B B' ρ y = a := by linear_combination a * a4 - a' * κ B B' ρ y * a5
    rw [← k]; ring
  refine ⟨g, ⟨hU, fun i ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_),
    fun i j k ↦ Units.ext (sec_ext _ _ _ fun B _ y hy ↦ ?_)⟩, w, fun i j B _ y hi hj ↦ ?_, h2⟩
  · have hy' : Inn y (U i) := hy
    refine (valR_resU _ hy' _).trans (Eq.trans ?_ (valR_one y _ hy').symm)
    rw [← hg i i B y (hy'.inf hy'), mul_inv_cancel, Units.val_one]
  · have hy' : Inn y (U i ⊓ U j ⊓ U k) := hy
    have hi : Inn y (U i) := hy'.mono (inf_le_left.trans inf_le_left)
    have hj : Inn y (U j) := hy'.mono (inf_le_left.trans inf_le_right)
    have hk : Inn y (U k) := hy'.mono inf_le_right
    refine (valR_mul y _ hy' _ _).trans ((congrArg₂ (· * ·) (valR_resU _ hy' _) (valR_resU _ hy' _)).trans
      (Eq.trans ?_ (valR_resU _ hy' _).symm))
    change valR y (U i ⊓ U j) (g i j).val * valR y (U j ⊓ U k) (g j k).val = valR y (U i ⊓ U k) (g i k).val
    rw [← hg i j B y (hi.inf hj), ← hg j k B y (hj.inf hk), ← hg i k B y (hi.inf hk), ← Units.val_mul]
    congr 1
    group
  · change _ = valR y (U i ⊓ U j) (g i j).val * _
    rw [← hg i j B y (hi.inf hj), ← Units.val_mul, inv_mul_cancel_right]

theorem Rel.exists_of_triv (h : Rel N κ) (ht : ∃ t : LB.Gen N, t.IsGen) :
    ∃ W V : N.ι → ∀ (B : Type) [CommRing B], (Sp B ⟶ Y) → B,
      (∀ (i : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → W i B y * V i B y = 1) ∧
      (∀ (i j : N.ι) (B : Type) [CommRing B] (y : Sp B ⟶ Y), Inn y (N.U i) → Inn y (N.U j) → W i B y = W j B y) ∧
      ∀ (i : N.ι) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y), Inn y (N.U i) →
        W i B' (spMap ρ ≫ y) = ρ (W i B y) * κ B B' ρ y := by
  obtain ⟨w, h1, h2⟩ := h
  obtain ⟨t, ht⟩ := ht
  refine ⟨fun i B _ y ↦ (w i B y).val * valR y (N.U i) ((t.s i)⁻¹).val,
    fun i B _ y ↦ ((w i B y)⁻¹).val * valR y (N.U i) (t.s i).val, fun i B _ y hi ↦ ?_, fun i j B _ y hi hj ↦ ?_,
    fun i B B' _ _ ρ y hi ↦ ?_⟩
  · have a := valR_inv_mul hi (t.s i)
    have b : (w i B y).val * ((w i B y)⁻¹).val = 1 := Units.mul_inv _
    linear_combination (w i B y).val * ((w i B y)⁻¹).val * a + b
  · have a := valR_inv_mul hi (t.s i)
    have b := valR_inv_mul hj (t.s j)
    have hy := hi.inf hj
    have c := congrArg (fun u : Γ(Y, N.U i ⊓ N.U j)ˣ ↦ valR y (N.U i ⊓ N.U j) u.val) (ht i j)
    simp only [Units.val_mul] at c
    rw [valR_mul _ _ hy, valR_resU _ hy, valR_resU _ hy] at c
    have d := h1 i j B y hi hj
    rw [c] at a
    simp only
    rw [d]
    generalize valR y (N.U i ⊓ N.U j) (N.g i j).val = G at *
    generalize valR y (N.U i) ((t.s i)⁻¹).val = p at *
    generalize valR y (N.U j) ((t.s j)⁻¹).val = q at *
    generalize valR y (N.U j) (t.s j).val = r at *
    have k : G * p = q := by linear_combination q * a - G * p * b
    rw [← k]; ring
  · simp only
    rw [h2 i B B' ρ y hi, valR_spMap_comp _ _ _ hi, map_mul]
    ring

end CrystallinePoints.Pd
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y : Scheme.{0}}

def pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : R →+* B := (Spec.preimage y).hom

theorem spMap_pre {B : Type} [CommRing B] (y : Sp B ⟶ Sp R) : spMap (pre y) = y := Spec.map_preimage y

theorem pre_spMap {B : Type} [CommRing B] (ρ : R →+* B) : pre (spMap ρ) = ρ :=
  congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom ρ))

theorem pre_comp {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Sp R) :
    pre (spMap ρ ≫ y) = ρ.comp (pre y) := by
  conv_lhs => rw [← spMap_pre y, ← GlobalTheory.Cris.spMap_comp, pre_spMap]

theorem valR_cst {B : Type} [CommRing B] (t : Y ⟶ Sp R) (y : Sp B ⟶ Y) (r : R) :
    valR y ⊤ (GlobalTheory.AbLaw.cst t ⊤ r) = pre (y ≫ t) r :=
  (valR_res y le_top (le_preimage_top y) _).trans
    ((valR_comp y t ⊤ _).symm.trans (preimage_apply (y ≫ t) r).symm)

@[reducible] def ptOf (s : X ⟶ Sp R) {B : Type} [CommRing B] (x : Sp B ⟶ X) : Pt s where
  B := B
  alg := (pre (x ≫ s)).toAlgebra
  x := x
  w := (spMap_pre _).symm

def homOf (s : X ⟶ Sp R) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) (x' : Sp B' ⟶ X)
    (h : spMap ρ ≫ x = x') : ptOf s x ⟶ ptOf s x' :=
  letI : Algebra R B := (pre (x ≫ s)).toAlgebra
  letI : Algebra R B' := (pre (x' ≫ s)).toAlgebra
  { ρ := { ρ with
      commutes' := fun r ↦ by
        change ρ (pre (x ≫ s) r) = pre (x' ≫ s) r
        rw [← h, Category.assoc, pre_comp]
        rfl }
    pt := h }

variable {s : X ⟶ Sp R}

def cv (z : Z1 (FP s)) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) : B' :=
  z.1 _ _ (homOf s ρ x _ rfl)

theorem cv_homOf (z : Z1 (FP s)) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X)
    (x' : Sp B' ⟶ X) (h : spMap ρ ≫ x = x') : (z.1 _ _ (homOf s ρ x x' h) : B') = cv z ρ x := by
  subst h
  rfl

theorem cv_eq (z : Z1 (FP s)) {P Q : Pt s} (φ : P ⟶ Q) :
    (z.1 P Q φ : Q.B) = cv z (φ.ρ : P.B →+* Q.B) P.x := by
  rw [← cv_homOf z _ _ _ φ.pt]
  obtain @⟨B, rB, aB, x, w⟩ := P
  obtain @⟨B', rB', aB', x', w'⟩ := Q
  have e : aB = (pre (x ≫ s)).toAlgebra := Algebra.algebra_ext _ _ fun r ↦ by
    change _ = pre (x ≫ s) r
    rw [w, pre_spMap]
  have e' : aB' = (pre (x' ≫ s)).toAlgebra := Algebra.algebra_ext _ _ fun r ↦ by
    change _ = pre (x' ≫ s) r
    rw [w', pre_spMap]
  subst e
  subst e'
  exact congrArg (z.1 _ _) (hom_ext fun _ ↦ rfl)

section
variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']

theorem cv_comp (z : Z1 (FP s)) (ρ : B →+* B') (τ : B' →+* B'') (x : Sp B ⟶ X) :
    cv z (τ.comp ρ) x = τ (cv z ρ x) + cv z τ (spMap ρ ≫ x) :=
  (cv_eq z (homOf s ρ x _ rfl ≫ homOf s τ (spMap ρ ≫ x) _ rfl)).symm.trans
    (Z1.comp z (homOf s ρ x _ rfl) (homOf s τ (spMap ρ ≫ x) _ rfl))

theorem cv_add (z z' : Z1 (FP s)) (ρ : B →+* B') (x : Sp B ⟶ X) : cv (z + z') ρ x = cv z ρ x + cv z' ρ x := rfl

theorem cv_smul (z : Z1 (FP s)) (r : R) (ρ : B →+* B') (x : Sp B ⟶ X) :
    cv (r • z) ρ x = ρ (pre (x ≫ s) r) * cv z ρ x := by
  change pre ((spMap ρ ≫ x) ≫ s) r * cv z ρ x = _
  rw [Category.assoc, pre_comp]
  rfl

theorem cv_pull {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (z : Z1 (FP s))
    (ρ : B →+* B') (x : Sp B ⟶ X') : cv ((pushC h).pullbackOneCocycle z) ρ x = cv z ρ (x ≫ φ) :=
  cv_eq z (pushHom h (homOf s' ρ x _ rfl))

theorem cv_of_mk_eq {z z' : Z1 (FP s)} (h : H1.mk _ z = H1.mk _ z') :
    ∃ g : ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B, ∀ (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B')
      (x : Sp B ⟶ X), cv z ρ x = cv z' ρ x + (g B' (spMap ρ ≫ x) - ρ (g B x)) := by
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h
  refine ⟨fun B _ x ↦ g (ptOf s x), fun B B' _ _ ρ x ↦ ?_⟩
  have e : (g (ptOf s (spMap ρ ≫ x)) : B') - ρ (g (ptOf s x)) = cv z ρ x - cv z' ρ x :=
    congrFun (congrFun (congrFun hg _) _) (homOf s ρ x _ rfl)
  linear_combination -e

end

open Classical in

def gam (z : Z1 (FP s)) (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X) : B :=
  if h : Inn x U.1 then
    cv z (B := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom (GlobalTheory.CechDR.affPt s U) else 0

theorem gam_map (z : Z1 (FP s)) (U : X.affineOpens) {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B')
    {x : Sp B ⟶ X} (h : Inn x U.1) : gam z U B' (spMap ρ ≫ x) = ρ (gam z U B x) + cv z ρ x := by
  have e : (valMap (spMap ρ ≫ x) U.1 (h.map ρ)).hom = ρ.comp (valMap x U.1 h).hom := RingHom.ext fun f ↦ by
    rw [← valR_eq, valR_spMap_comp _ _ _ h, valR_eq _ _ h]
    rfl
  have e' : spMap (R := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom ≫ GlobalTheory.CechDR.affPt s U = x :=
    specMap_valMap_fromSpec U.2 x h
  rw [gam, gam, dif_pos h, dif_pos (h.map ρ), e]
  exact (cv_comp z (B := GlobalTheory.CechDR.Sec s U.1) (valMap x U.1 h).hom ρ _).trans (by rw [e'])

theorem eq_of_cover {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤) {B : Type} [CommRing B] (x : Sp B ⟶ X)
    (b b' : B) (H : ∀ (j : J) (C : Type) [CommRing C] (τ : B →+* C), Inn (spMap τ ≫ x) (U j) → τ b = τ b') :
    b = b' := by
  have hc : ⨆ j, x ⁻¹ᵁ U j = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  have e := sec_ext_cover (fun j ↦ x ⁻¹ᵁ U j) hc ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b') fun j C _ y _ hy ↦ by
      rw [← preimage_apply, ← preimage_apply]
      refine H j C (pre y) ?_
      rw [spMap_pre]
      exact hy
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1 e

theorem mk_eq_zero_of_cover (z : Z1 (FP s)) {J : Type} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (G : J → ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B)
    (h1 : ∀ (i j : J) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x (U i) → Inn x (U j) → G i B x = G j B x)
    (h2 : ∀ (i : J) (B B' : Type) [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X), Inn x (U i) →
      G i B' (spMap ρ ≫ x) = ρ (G i B x) + cv z ρ x) : H1.mk _ z = 0 := by
  classical
  let G₀ : ∀ (B : Type) [CommRing B], (Sp B ⟶ X) → B := fun B _ x ↦
    if h : ∃ j, Inn x (U j) then G h.choose B x else 0
  have hG : ∀ (j : J) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x (U j) → G₀ B x = G j B x := by
    intro j B _ x hx
    have h : ∃ j, Inn x (U j) := ⟨j, hx⟩
    simp only [G₀, dif_pos h]
    exact h1 _ _ B x h.choose_spec hx
  have ex : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ X), ∃ g : B, ∀ (j : J) (C : Type) [CommRing C] (τ : B →+* C),
      Inn (spMap τ ≫ x) (U j) → τ g = G j C (spMap τ ≫ x) - cv z τ x := by
    intro B _ x
    have hc : ⨆ j, x ⁻¹ᵁ U j = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
    obtain ⟨f, hf⟩ := exists_sec_cover (fun j ↦ x ⁻¹ᵁ U j) ⊤ (fun _ ↦ le_top) hc.ge
      (fun C _ y ↦ G₀ C (y ≫ x) - cv z (pre y) x) fun j C C' _ _ τ y hy ↦ by
        have hy' : Inn (y ≫ x) (U j) := hy
        rw [Category.assoc, hG j _ _ hy', hG j _ _ (hy'.map τ), h2 j _ _ τ _ hy', pre_comp, cv_comp, spMap_pre,
          map_sub]
        ring
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f, fun j C _ τ hτ ↦ ?_⟩
    have a := hf j C (spMap τ) hτ
    have b := valR_specMap (CommRingCat.ofHom τ) ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f)
    have c : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom f) = f := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    rw [c] at b
    rw [pre_spMap, hG j _ _ hτ] at a
    exact b.symm.trans a.symm
  choose g hg using ex
  refine H1.mk_eq_zero.2 ⟨fun P ↦ g P.B P.x, ?_⟩
  funext P Q φ
  rw [cv_eq z φ]
  change (g Q.B Q.x - φ.ρ (g P.B P.x) : Q.B) = _
  refine eq_of_cover U hU Q.x _ _ fun j C _ τ hτ ↦ ?_
  have e : spMap (τ.comp (φ.ρ : P.B →+* Q.B)) ≫ P.x = spMap τ ≫ Q.x := by
    rw [GlobalTheory.Cris.spMap_comp, Category.assoc, φ.pt]
  have a := hg Q.B Q.x j C τ hτ
  have b := hg P.B P.x j C (τ.comp (φ.ρ : P.B →+* Q.B)) (e ▸ hτ)
  rw [e, cv_comp, φ.pt] at b
  have b' : τ (φ.ρ (g P.B P.x)) = _ := b
  rw [map_sub, a, b']
  ring

end CrystallinePoints.Pd
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.Points

namespace CrystallinePoints.Pd

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp R}

def oneAdd {B : Type} [CommRing B] (e a : B) (h : e * e = 0) : Bˣ :=
  ⟨1 + e * a, 1 - e * a, by linear_combination -(a * a) * h, by linear_combination -(a * a) * h⟩

theorem val_sq {B : Type} [CommRing B] (y : Sp B ⟶ Y) {η : Γ(Y, ⊤)} (hη : η * η = 0) :
    valR y ⊤ η * valR y ⊤ η = 0 := by
  rw [← valR_mul _ _ (le_preimage_top y), hη, valR_zero _ _ (le_preimage_top y)]

theorem map_val_sq {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (y : Sp B ⟶ Y) {η : Γ(Y, ⊤)}
    (hη : η * η = 0) : ρ (valR y ⊤ η) * ρ (valR y ⊤ η) = 0 := by
  rw [← map_mul, val_sq y hη, map_zero]

def kap (z : Z1 (FP s)) (π : Y ⟶ X) (η : Γ(Y, ⊤)) : Kap Y :=
  fun _ _ _ _ ρ y ↦ 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)

theorem aff_cover (π : Y ⟶ X) : ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

theorem exists_bundle (z : Z1 (FP s)) (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0) :
    ∃ g : ∀ U V : X.affineOpens, Γ(Y, π ⁻¹ᵁ U.1 ⊓ π ⁻¹ᵁ V.1)ˣ,
      LB.IsLB ⟨X.affineOpens, fun U ↦ π ⁻¹ᵁ U.1, g⟩ ∧ Rel ⟨X.affineOpens, fun U ↦ π ⁻¹ᵁ U.1, g⟩ (kap z π η) := by
  refine exists_rel (fun U : X.affineOpens ↦ π ⁻¹ᵁ U.1) (aff_cover π) (kap z π η)
    (fun U B _ y ↦ oneAdd (valR y ⊤ η) (gam z U B (y ≫ π)) (val_sq y hη)) fun U B B' _ _ ρ y hy ↦ ?_
  have hy' : Inn (y ≫ π) U.1 := hy
  change 1 + valR (spMap ρ ≫ y) ⊤ η * gam z U B' ((spMap ρ ≫ y) ≫ π) =
    ρ (1 + valR y ⊤ η * gam z U B (y ≫ π)) * (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π))
  rw [Category.assoc, gam_map z U ρ hy', valR_spMap_comp _ _ _ (le_preimage_top y), map_add, map_mul, map_one]
  linear_combination -(ρ (gam z U B (y ≫ π)) * cv z ρ (y ≫ π)) * map_val_sq ρ y hη

theorem rel_of_mk_eq {z z' : Z1 (FP s)} (h : H1.mk _ z = H1.mk _ z') (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0)
    {N : LB Y} (hN : Rel N (kap z' π η)) : Rel N (kap z π η) := by
  obtain ⟨g, hg⟩ := cv_of_mk_eq h
  refine hN.twist (fun B _ y ↦ oneAdd (valR y ⊤ η) (g B (y ≫ π)) (val_sq y hη)) fun B B' _ _ ρ y ↦ ?_
  change (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)) * ρ (1 + valR y ⊤ η * g B (y ≫ π)) =
    (1 + ρ (valR y ⊤ η) * cv z' ρ (y ≫ π)) * (1 + valR (spMap ρ ≫ y) ⊤ η * g B' ((spMap ρ ≫ y) ≫ π))
  rw [Category.assoc, hg, valR_spMap_comp _ _ _ (le_preimage_top y), map_add, map_mul, map_one]
  linear_combination ((cv z' ρ (y ≫ π) + (g B' (spMap ρ ≫ y ≫ π) - ρ (g B (y ≫ π)))) * ρ (g B (y ≫ π)) -
    cv z' ρ (y ≫ π) * g B' (spMap ρ ≫ y ≫ π)) * map_val_sq ρ y hη

theorem exists_class (s : X ⟶ Sp R) (c : H1OnPoints s) (π : Y ⟶ X) (η : Γ(Y, ⊤)) (hη : η * η = 0) :
    ∃ p : Pic Y, ∀ (z : Z1 (FP s)) (N : LB Y) (hN : N.IsLB), H1.mk _ z = c → Rel N (kap z π η) → p = cls N hN := by
  obtain ⟨z₀, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, h₀, r₀⟩ := exists_bundle z₀ π hη
  exact ⟨cls _ h₀, fun z N hN e r ↦ Rel.cls_eq h₀ hN (rel_of_mk_eq e π hη r₀) r⟩

def Ecl : ETy := fun s c _ π η hη ↦ (exists_class s c π η hη).choose

theorem Ecl_eq (z : Z1 (FP s)) (π : Y ⟶ X) {η : Γ(Y, ⊤)} (hη : η * η = 0) {N : LB Y} (hN : N.IsLB)
    (r : Rel N (kap z π η)) : Ecl s (H1.mk _ z) π η hη = cls N hN :=
  (exists_class s _ π η hη).choose_spec z N hN rfl r

section Inj

variable {π : Y ⟶ X} {t : Y ⟶ Sp (DualNumber R)} (hp : IsPullback π t s (spMap (algebraMap R (DualNumber R))))

def yeps {B : Type} [CommRing B] (x : Sp B ⟶ X) : Sp (DualNumber B) ⟶ Y :=
  hp.lift (spMap (algebraMap B (DualNumber B)) ≫ x) (spMap (dualMap (pre (x ≫ s)))) (by
    rw [← GlobalTheory.Cris.spMap_comp, dualMap_comp_algebraMap, GlobalTheory.Cris.spMap_comp (pre (x ≫ s)) (algebraMap B (DualNumber B)),
      spMap_pre, Category.assoc])

theorem yeps_fst {B : Type} [CommRing B] (x : Sp B ⟶ X) :
    yeps hp x ≫ π = spMap (algebraMap B (DualNumber B)) ≫ x := hp.lift_fst _ _ _

theorem yeps_snd {B : Type} [CommRing B] (x : Sp B ⟶ X) : yeps hp x ≫ t = spMap (dualMap (pre (x ≫ s))) :=
  hp.lift_snd _ _ _

theorem yeps_map {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B') (x : Sp B ⟶ X) :
    yeps hp (spMap ρ ≫ x) = spMap (dualMap ρ) ≫ yeps hp x := by
  refine hp.hom_ext ?_ ?_
  · rw [yeps_fst, Category.assoc, yeps_fst, ← Category.assoc, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp,
      ← GlobalTheory.Cris.spMap_comp, dualMap_comp_algebraMap]
  · rw [yeps_snd, Category.assoc, Category.assoc, yeps_snd, ← GlobalTheory.Cris.spMap_comp, dualMap_comp_dualMap, pre_comp]

theorem valR_yeps {B : Type} [CommRing B] (x : Sp B ⟶ X) : valR (yeps hp x) ⊤ (epsFn t) = DualNumber.eps := by
  rw [epsFn, valR_cst, yeps_snd, pre_spMap]
  ext <;> simp [dualMap]

include hp in
theorem mk_eq_zero_of_triv (z : Z1 (FP s)) (h : Ecl s (H1.mk _ z) π (epsFn t) (epsFn_sq t) = 0) : H1.mk _ z = 0 := by
  obtain ⟨g, hN, r⟩ := exists_bundle z π (epsFn_sq t)
  rw [Ecl_eq z π _ hN r, cls_eq_zero_iff] at h
  obtain ⟨W, V, h0, h1, h2⟩ := r.exists_of_triv h
  have hin : ∀ (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x U.1 →
      Inn (yeps hp x) (π ⁻¹ᵁ U.1) := fun U B _ x hx ↦ by
    have : Inn (yeps hp x ≫ π) U.1 := by rw [yeps_fst]; exact hx.map _
    exact this
  have h0' : ∀ (U : X.affineOpens) (B : Type) [CommRing B] (x : Sp B ⟶ X), Inn x U.1 →
      (W U _ (yeps hp x)).fst * (V U _ (yeps hp x)).fst = 1 := fun U B _ x hx ↦ by
    rw [← TrivSqZeroExt.fst_mul, h0 U _ _ (hin U B x hx), TrivSqZeroExt.fst_one]
  refine mk_eq_zero_of_cover z (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U B _ x ↦ (W U _ (yeps hp x)).snd * (V U _ (yeps hp x)).fst - (cv z (algebraMap B (DualNumber B)) x).fst)
    (fun U U' B _ x hx hx' ↦ ?_) fun U B B' _ _ ρ x hx ↦ ?_
  · have a := h0' U B x hx
    have b := h0' U' B x hx'
    have e := h1 U U' _ _ (hin U B x hx) (hin U' B x hx')
    rw [e] at a ⊢
    linear_combination (W U' _ (yeps hp x)).snd * ((V U' _ (yeps hp x)).fst * a - (V U _ (yeps hp x)).fst * b)
  · have a := congrArg ρ (h0' U B x hx)
    have b := h0' U B' _ (hx.map ρ)
    have e := h2 U _ _ (dualMap ρ) _ (hin U B x hx)
    rw [← yeps_map] at e
    have e' : W U _ (yeps hp (spMap ρ ≫ x)) = dualMap ρ (W U _ (yeps hp x)) *
        (1 + dualMap ρ (valR (yeps hp x) ⊤ (epsFn t)) * cv z (dualMap ρ) (yeps hp x ≫ π)) := e
    rw [valR_yeps, yeps_fst] at e'
    have c1 := cv_comp z (algebraMap B (DualNumber B)) (dualMap ρ) x
    rw [dualMap_comp_algebraMap, cv_comp] at c1
    have f : ∀ c : DualNumber B, (dualMap ρ c).fst = ρ c.fst := fun _ ↦ add_zero _
    have sn : ∀ c : DualNumber B, (dualMap ρ c).snd = ρ c.snd := fun _ ↦ zero_add _
    have c2 := congrArg TrivSqZeroExt.fst c1
    have e1 := congrArg TrivSqZeroExt.fst e'
    have e2 := congrArg TrivSqZeroExt.snd e'
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add, DualNumber.snd_mul, f, sn,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, DualNumber.fst_eps, DualNumber.snd_eps, map_zero,
      map_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, zero_mul, add_zero, zero_add, mul_one, one_mul,
      map_mul] at c2 e1 e2 a
    simp only [map_sub, map_mul]
    rw [e1] at b
    rw [e2]
    generalize ρ (W U _ (yeps hp x)).fst = w₀ at *
    generalize ρ (W U _ (yeps hp x)).snd = w₁ at *
    generalize ρ (V U _ (yeps hp x)).fst = v at *
    generalize (V U _ (yeps hp (spMap ρ ≫ x))).fst = v' at *
    have k : v' = v := by linear_combination v * b - v' * a
    rw [k]
    linear_combination (cv z (dualMap ρ) (spMap (algebraMap B (DualNumber B)) ≫ x)).fst * a - c2

end Inj

theorem exists_isE : ∃ E : ETy, IsE @E := by
  refine ⟨@Ecl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _ X s c Y Y' π η hη ψ η' hη' e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, r⟩ := exists_bundle z π hη
    rw [Ecl_eq z π hη hN r, ← cls_pull hN ψ (pull_isLB hN ψ)]
    refine (Ecl_eq z _ hη' _ ((r.pull ψ).congr fun B B' _ _ ρ y ↦ ?_)).symm
    have k : valR y ⊤ η' = valR (y ≫ ψ) ⊤ η := by rw [e]; exact (valR_comp y ψ ⊤ η).symm
    change 1 + ρ (valR y ⊤ η') * cv z ρ (y ≫ ψ ≫ π) = 1 + ρ (valR (y ≫ ψ) ⊤ η) * cv z ρ ((y ≫ ψ) ≫ π)
    rw [k, Category.assoc]
  · intro R _ X s c c' Y π η hη
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨z', rfl⟩ := H1.mk_surjective _ c'
    obtain ⟨g, hN, r⟩ := exists_bundle (z + z') π hη
    obtain ⟨g', hN', r'⟩ := exists_bundle z' π hη
    have rd := r.div (κ'' := kap z π η) r' fun B B' _ _ ρ y ↦ by
      change (1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π)) * (1 + ρ (valR y ⊤ η) * cv z' ρ (y ≫ π)) =
        1 + ρ (valR y ⊤ η) * cv (z + z') ρ (y ≫ π)
      rw [cv_add]
      linear_combination (cv z ρ (y ≫ π) * cv z' ρ (y ≫ π)) * map_val_sq ρ y hη
    rw [← map_add, Ecl_eq _ π hη hN r, Ecl_eq _ π hη hN' r', Ecl_eq _ π hη (LB.isLB_div hN hN') rd,
      cls_div hN hN', sub_add_cancel]
  · intro R _ X s c r Y π η hη η' hη' e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z π hη'
    rw [← map_smul, Ecl_eq _ π hη' hN rN]
    refine Ecl_eq _ π hη hN (rN.congr fun B B' _ _ ρ y ↦ ?_)
    change 1 + ρ (valR y ⊤ η) * cv (r • z) ρ (y ≫ π) = 1 + ρ (valR y ⊤ η') * cv z ρ (y ≫ π)
    rw [cv_smul, e, valR_mul _ _ (le_preimage_top y), valR_cst, map_mul, Category.assoc]
    ring
  · intro R R' _ _ X X' s s' σ φ h c Y π η hη
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z (π ≫ φ) hη
    rw [Ecl_eq _ _ hη hN rN]
    refine Ecl_eq ((pushC h).pullbackOneCocycle z) π hη hN (rN.congr fun B B' _ _ ρ y ↦ ?_)
    change 1 + ρ (valR y ⊤ η) * cv ((pushC h).pullbackOneCocycle z) ρ (y ≫ π) = 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π ≫ φ)
    rw [cv_pull, Category.assoc]
  · intro R _ X s c Y π η hη e
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hN, rN⟩ := exists_bundle z π hη
    rw [Ecl_eq _ _ hη hN rN, cls_eq_zero_iff]
    refine rN.triv fun B B' _ _ ρ y ↦ ?_
    change 1 + ρ (valR y ⊤ η) * cv z ρ (y ≫ π) = 1
    rw [e, valR_zero _ _ (le_preimage_top y), map_zero, zero_mul, add_zero]
  · intro R _ X s c Y π t hp h
    obtain ⟨z, rfl⟩ := H1.mk_surjective _ c
    exact mk_eq_zero_of_triv hp z h

end CrystallinePoints.Pd
end
end
