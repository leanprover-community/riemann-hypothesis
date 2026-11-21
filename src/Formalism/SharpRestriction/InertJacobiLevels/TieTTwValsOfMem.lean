import Formalism.SharpRestriction.InertJacobiLevels.VVEqEmptyOfNotIsResidueClassZero
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain

section Drop

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (Cr : ℝ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

def tieL : SizeData₂ D := tieWeightData L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

def tieX : G.Inst D (tieL L0 X0 K Cr len hw hg hu) := tieInst L0 X0 K {p | NoGain X0 K Cr p} len hw hg hu

theorem tieL_drop_iff (p : ℕ) :
    p ∈ (tieL L0 X0 K Cr len hw hg hu).drop ↔
      NoGain (tieX L0 X0 K Cr len hw hg hu) K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T :=
  Iff.rfl

theorem tieL_supp_sat (w : D.what₂.places.Pl)
    (h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ (tieL L0 X0 K Cr len hw hg hu).sc.X'' D.R.n) :
    w ∈ (tieL L0 X0 K Cr len hw hg hu).supp :=
  tie_supp_sat L0 X0 K _ len hw hg hu w h

theorem tieL_fills
    (hf : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D),
      (D.eTau τ : D.R.GG) = G.plGG D z → G.fill X0 (G.bL L0) j z = wj D j τ)
    (w : D.what₂.places.Pl) : G.ParametersFill (tieX L0 X0 K Cr len hw hg hu) K w :=
  tie_fills L0 X0 K _ len hw hg hu hf w


end Drop

structure FieldData where
  φ : Formalism.HC.Frame
  E : Type
  [fld : Field E]
  [nf : NumberField E]
  gal : (E ≃ₐ[ℚ] E) ≃* φ.GG
  N : ℕ
  ζ : CyclotomicField N ℚ
  a : E
  b : E

attribute [instance] FieldData.fld FieldData.nf

def FieldData.e (F : FieldData) : ℕ := F.φ.e

abbrev FieldData.Lf (F : FieldData) : Type := F.E

def FieldData.hval (F : FieldData) (p : ℕ) : ℕ :=
  (F.φ.iotaInv (Classical.epsilon (fun g : F.φ.GG =>
    ∃ (P : Ideal (𝓞 F.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : F.E ≃ₐ[ℚ] F.E), IsArithFrobAt ℤ σ P ∧ F.gal σ = g)).2).val

def fieldDataH (x : Σ R : Ranks, Host R) : FieldData :=
  ⟨x.1.toFrame, x.2.E, x.2.gal, x.2.condN, x.2.cycZeta, x.2.sqq, x.2.sqd⟩

def fieldData (D : D7) : FieldData := fieldDataH ⟨D.R, D.host⟩












section Totals

variable {D : D7} (L0 : SizeData₂ D) (X0 : G.Inst D L0) (K : G.Consts) (dr : Set ℕ)
  (len : D.what₂.Word → D.what₂.places.Pl → ℚ) (hw : 1 ≤ L0.sc.w'' D.R.n)
  (hg : ∀ i, ¬ (G.IsResidueClassZero D (D.host.g i) ∨ G.IsSg D (D.host.g i)))
  (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L0 j w = 0)

theorem mem_suppAt_below (p : ℕ) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) (w : D.what₂.places.Pl) :
    w ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p ↔ D.what₂.places.resChar w = p := by
  unfold suppAt
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨tie_supp_sat L0 X0 K dr len hw hg hu w (by rw [h]; exact hle), h⟩

theorem sum_sz_const (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (c : ℝ) :
    ∑ w ∈ S, SizeData₂.sz w c = 2 * Real.log p * c := by
  have h := factEtaMean D p hp S hS
  unfold SizeData₂.sz SizeData₂.lwP
  rw [← h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring

open Classical in

theorem tie_gainTot_below (p : ℕ) (hp : p.Prime) (hle : (p : ℝ) ≤ L0.sc.X'' D.R.n) :
    gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = 2 * Real.log p *
      ((if G.IsResidueClassZero D p ∨ G.IsSg D p then ∑ j ∈ SizeData₂.lifts D, G.gainP X0 K (G.aL L0) (G.bL L0) p j else 0) -
        G.tauP X0 K (G.aL L0) (G.bL L0) p) := by
  have hS := mem_suppAt_below L0 X0 K dr len hw hg hu p hle
  rw [← sum_sz_const p hp _ hS]
  unfold gainTot
  refine Finset.sum_congr rfl (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (hS w).1 hw'
  have hws : w ∈ tieSupp L0 := (Finset.mem_filter.1 hw').1
  congr 1
  show (∑ j ∈ SizeData₂.lifts D, if w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D (D.what₂.places.resChar w) ∨
      G.IsSg D (D.what₂.places.resChar w)) then
        G.gainP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) j else 0) -
      G.tauP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) = _
  rw [hwp]
  by_cases hin : G.IsResidueClassZero D p ∨ G.IsSg D p
  · simp only [if_pos hin, if_pos (And.intro hws hin)]
  · simp only [if_neg hin, if_neg (fun h : w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D p ∨ G.IsSg D p) => hin h.2),
      Finset.sum_const_zero]

theorem gainP_eq_zero_of_lt (a b : G.HH D → ℤ) (p j : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) :
    G.gainP X0 K a b p j = 0 := by
  unfold G.gainP
  rw [if_pos (Or.inr h)]

open Classical in

theorem tie_gainTot_above (p : ℕ) (h : L0.sc.X'' D.R.n < (p : ℝ)) :
    gainTot (tieWeightData L0 X0 K dr len hw hg hu) p = 0 := by
  unfold gainTot
  refine Finset.sum_eq_zero (fun w hw' => ?_)
  have hwp : D.what₂.places.resChar w = p := (Finset.mem_filter.1 hw').2
  have e : (∑ j ∈ SizeData₂.lifts D, (tieWeightData L0 X0 K dr len hw hg hu).gain j w) -
      (tieWeightData L0 X0 K dr len hw hg hu).tau w = 0 := by
    show (∑ j ∈ SizeData₂.lifts D, if w ∈ tieSupp L0 ∧ (G.IsResidueClassZero D (D.what₂.places.resChar w) ∨
      G.IsSg D (D.what₂.places.resChar w)) then
        G.gainP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) j else 0) -
      G.tauP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) = 0
    rw [hwp, tauP_above L0 X0 K _ _ _ h, sub_zero]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [gainP_eq_zero_of_lt L0 X0 K _ _ _ _ h, ite_self]
  rw [e]
  simp [SizeData₂.sz]



theorem tie_TTw_vals (w : D.what₂.places.Pl) :
    ((tieWeightData L0 X0 K dr len hw hg hu).TTw w).image (fun t : D.host.TT => (t : D.R.A).val) =
      (G.TTP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w)).image Formalism.HC.Frame.A.val := by
  have h : ((tieWeightData L0 X0 K dr len hw hg hu).TTw w).map (Function.Embedding.subtype _) =
      G.TTP X0 K (G.aL L0) (G.bL L0) (D.what₂.places.resChar w) :=
    Finset.subtype_map_of_mem (TTP_subset L0 X0 K _ _ _)
  rw [← h, Finset.map_eq_image, Finset.image_image]
  rfl

theorem tie_TTwVals_of_mem (p : ℕ) (w0 : D.what₂.places.Pl)
    (h0 : w0 ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p = {(G.TTP X0 K (G.aL L0) (G.bL L0) p).image Formalism.HC.Frame.A.val} := by
  unfold TTwVals
  ext s
  rw [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw', rfl⟩
    rw [tie_TTw_vals, (Finset.mem_filter.1 hw').2]
  · rintro rfl
    refine ⟨w0, h0, ?_⟩
    rw [tie_TTw_vals, (Finset.mem_filter.1 h0).2]


def UnderSupp (p : ℕ) : Prop :=
  (p : ℝ) ≤ L0.sc.X'' D.R.n ∨ p ∈ ({D.host.d, D.host.g 0, D.host.g 1} : Finset ℕ) ∨
    ∃ w ∈ L0.supp, D.what₂.places.resChar w = p

open Classical in

theorem tie_TTwVals (p : ℕ) (hp : p.Prime) :
    TTwVals (tieWeightData L0 X0 K dr len hw hg hu) p =
      if UnderSupp L0 p then {(G.TTP X0 K (G.aL L0) (G.bL L0) p).image Formalism.HC.Frame.A.val} else ∅ := by
  by_cases h : UnderSupp L0 p
  · rw [if_pos h]
    have hex : ∃ w0, w0 ∈ suppAt (tieWeightData L0 X0 K dr len hw hg hu) p := by
      rcases h with h | h | ⟨w, hw', hwp⟩
      · obtain ⟨w0, h0⟩ := exists_place_over D p hp
        exact ⟨w0, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w0).2 (Or.inl (by rw [h0]; exact h)), h0⟩⟩
      · obtain ⟨w0, h0⟩ := exists_place_over D p hp
        exact ⟨w0, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w0).2 (Or.inr (Or.inl (by rw [h0]; exact h))), h0⟩⟩
      · exact ⟨w, Finset.mem_filter.2 ⟨(mem_tieSupp L0 w).2 (Or.inr (Or.inr hw')), hwp⟩⟩
    obtain ⟨w0, h0⟩ := hex
    exact tie_TTwVals_of_mem L0 X0 K dr len hw hg hu p w0 h0
  · rw [if_neg h]
    unfold TTwVals
    rw [Finset.image_eq_empty]
    unfold suppAt
    rw [Finset.filter_eq_empty_iff]
    intro w hw' hwp
    apply h
    rcases (mem_tieSupp L0 w).1 hw' with h1 | h1 | h1
    · exact Or.inl (by rw [← hwp]; exact h1)
    · exact Or.inr (Or.inl (by rw [← hwp]; exact h1))
    · exact Or.inr (Or.inr ⟨w, h1, hwp⟩)

end Totals

end Formalism.MainNotions.Inhab

end
