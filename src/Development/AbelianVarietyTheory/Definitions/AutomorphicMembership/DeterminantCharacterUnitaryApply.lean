import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowEqOneOfUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.Mem.Chr.DetGroupModel

section General

variable {L : Type} [Field L] [NumberField L]

theorem loc_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (x : v.adicCompletion L) v = _
  simp

theorem loc_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (x : v.adicCompletion L) w = _
  exact Function.update_of_ne h _ _

def valAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* WithZero (Multiplicative ℤ) where
  toFun a := Valued.v ((a : AdeleRing (𝓞 L) L).2 w)
  map_one' := by
    show Valued.v (1 : w.adicCompletion L) = 1
    exact map_one _
  map_mul' a b := by
    show Valued.v ((a : AdeleRing (𝓞 L) L).2 w * (b : AdeleRing (𝓞 L) L).2 w) = _
    exact map_mul _ _ _

theorem valAt_loc_self (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    valAt v (localIdele L v (atFin v k)) = v.valuation L (k : L) := by
  show Valued.v (((localIdele L v _ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = _
  rw [loc_self]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _

theorem valAt_loc_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    valAt w (localIdele L v x) = 1 := by
  show Valued.v (((localIdele L v _ : Ideles L) : AdeleRing (𝓞 L) L).2 w) = _
  rw [loc_ne h, map_one]

theorem valuation_unif (v : HeightOneSpectrum (𝓞 L)) : v.valuation L (unif v : L) = WithZero.exp (-1 : ℤ) := by
  have h : Valued.v (((unif v : Lˣ) : L) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h



theorem diag_eq (k : Lˣ) : diagUnits L k = infDiag k * finPartI L (diagUnits L k) := by
  classical
  apply Units.ext
  have h1 : ∀ s : Finset (InfinitePlace L), ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 ∧
      ∀ w', ((∏ w ∈ s, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w' =
        if w' ∈ s then algebraMap L w'.Completion (k : L) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨rfl, fun _ => rfl⟩
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine ⟨?_, fun w' => ?_⟩
      · show (1 : FiniteAdeleRing (𝓞 L) L) * _ = 1
        rw [one_mul]; exact ih.1
      · show (Pi.mulSingle (M := fun w : InfinitePlace L => w.Completion) a (algebraMap L a.Completion (k : L)) w') * _ = _
        rw [ih.2 w']
        by_cases h : w' = a
        · subst h; simp [ha]
        · simp [h]
  have h2 : infDiag k = ∏ w, infIdele L w (atInf w k) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]; rfl
  rw [h2]
  refine Prod.ext (funext fun w => ?_) ?_
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).1 w * 1
    rw [(h1 _).2 w, if_pos (Finset.mem_univ _), mul_one]; rfl
  · show _ = ((∏ w, infIdele L w (atInf w k) : Ideles L) : AdeleRing (𝓞 L) L).2 * _
    rw [(h1 _).1, one_mul]; rfl

theorem fin_diag (χ : HChar L) (k : Lˣ) : χ.1 (finPartI L (diagUnits L k)) = (χ.inf k)⁻¹ := by
  have h := χ.2.2 k
  rw [diag_eq, map_mul] at h
  exact eq_inv_of_mul_eq_one_right h




end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_conj (σ : H.E →+* ℂ) (z : H.E) : σ (H.conj z) = star (σ z) :=
  H.conjE_apply σ z

theorem conj_F (k : H.F) : H.conj (k : H.E) = k := (H.conjE_mem_hostF_iff _).1 k.2

def pack : DtPack H :=
  letI := H.cmStar
  { Dt := ℂˣ
    muTil := fun _ => MonoidHom.id _
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.1 hx
    e1Dt := (GlobalTheory.MemberDetLaws.det_laws R H).choose
    rest_detCharacter_on_unitary_eq := fun z => by
      have h := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.1 z
      rw [finprod_eq_prod_of_fintype] at h
      exact h
    relDet := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose
    relDet_self := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.1
    relDet_mul := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.2.1
    relDet_smul := (GlobalTheory.MemberDetLaws.det_laws R H).choose_spec.choose_spec.2.2.2 }




theorem valAt_locF (w : HeightOneSpectrum (𝓞 H.E)) (v : HeightOneSpectrum (𝓞 H.F)) (k : (H.F)ˣ) :
    open Classical in valAt w (locF H.F v k) = if w.under (𝓞 H.F) = v then w.valuation H.E ((k : H.F) : H.E) else 1 := by
  classical
  unfold locF
  rw [map_prod]
  have hm : ∀ Q, Q ∈ aboveF (L := H.E) H.F v ↔ Q.under (𝓞 H.F) = v := fun Q => by
    unfold aboveF; rw [Set.Finite.mem_toFinset]; rfl
  split_ifs with hw
  · rw [Finset.prod_eq_single w (fun Q _ hQ => valAt_loc_ne hQ.symm _) (fun h => absurd ((hm w).2 hw) h), valAt_loc_self]
    rfl
  · refine Finset.prod_eq_one fun Q hQ => valAt_loc_ne ?_ _
    rintro rfl
    exact hw ((hm _).1 hQ)

theorem under_eq {w w' : HeightOneSpectrum (𝓞 H.E)} (h : ConjPl H.conj.toRingEquiv w w') :
    w.under (𝓞 H.F) = w'.under (𝓞 H.F) := by
  ext x
  show algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ w.asIdeal ↔ algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ w'.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := H.E), ← h]
  have : H.conj.toRingEquiv (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) x)) =
      algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) x) := conj_F H (x : H.F)
  exact this ▸ Iff.rfl





theorem valuation_eq_exp {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    w.valuation L (k : L) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]


end GlobalTheory.Mem.Chr.DetGroupModel
