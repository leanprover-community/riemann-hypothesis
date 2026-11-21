import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoGeoScalIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

set_option maxHeartbeats 2000000 in

def restrict (hH : Holds z.R z.F) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resR h
  cG := z.cG
  geo := z.resGeo h
  pins := z.pins_resR h hc hH.aux.ex hH.prim.thmB
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le



theorem restrictRealData_constant_error (h : Wt' ⊆ Wt) : (z.resR h).kap = z.R.kap ∧ (z.resR h).err0 = z.R.err0 := ⟨rfl, rfl⟩

set_option maxHeartbeats 1000000 in

theorem restrictRealData_lift_scalar (h : Wt' ⊆ Wt) (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.resR h).lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := rfl


theorem restrict_holds (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Holds (z.restrict hH Wt' h hc).R (z.restrict hH Wt' h hc).F := z.holds_resR h hH

set_option maxHeartbeats 2000000 in

theorem inGeo_resGeo_iff (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.InGeo (z.resGeo h) ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  Res.inGeo_iff (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') (g := z.geo)


variable (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)

theorem mem_nonzero_index_places_iff_at_place_or_conjugate (w : X.B.places.Pl) :
    w ∈ z.W1 F0 ↔ ∃ j, NzAt z.R z.F F0 j (plB X w) ∨ NzAt z.R z.F F0 j (Formalism.DivisionValues.conjPl (plB X w)) := by
  refine exists_congr fun j => ⟨?_, ?_⟩
  · rintro ⟨w', rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem nonzero_index_places_conj_stable : ConjStable X (z.W1 F0) := by
  intro w hw
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate] at hw ⊢
  rw [plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  exact hw.imp fun _ h => h.symm

set_option maxHeartbeats 2000000 in

theorem nzAt_resR (h : Wt' ⊆ Wt) (j : Fin X.toD7.R.m) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    NzAt (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔ NzAt z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) F0 j v := by
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels, columnChoiceReferenceFace_eq_bareFaceTwoLevels]
  exact nzAt_res (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') (lev0 I) (chr0 I) (lev1 I) (chr1 I) F0 j v


theorem complex_side_places_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (N : IndefNum (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.base3) (hN : N.F0 = F0)
    (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr N (X.toD7.plEq w) ↔ w ∈ z.W1 F0 := by
  subst hN
  exact (complexSide_nonzeroIndexPlaces_iff z.R z.F kap lam err Dc Sp Zsc N (plB X w)).trans (z.mem_nonzero_index_places_iff_at_place_or_conjugate N.F0 w).symm

theorem complex_side_face_numbers_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0) (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
      (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) (X.toD7.plEq w) ↔ w ∈ z.W1 F0 :=
  z.complex_side_places_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc _ ((complexSide_numberContents_eq_scaleAtSubspaces z.R z.F kap lam err Dc Sp Zsc C CH).trans hZ) w

theorem twisted_places_eq_complex_side_of_eq_nonzero_index (hW : z.W1 F0 = Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0)
    (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ ((z.R.updS kap lam).withErr err).twPl ↔
      (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
        (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) v := by
  obtain ⟨w, rfl⟩ := (plB X).surjective v
  exact (z.plB_mem_twPl w).trans ((Set.ext_iff.1 hW w).symm.trans (z.complex_side_face_numbers_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc C CH hZ w).symm)

def restrictNonzero (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) := z.restrict hH (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)






set_option maxHeartbeats 4000000 in

def restrictE (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resRE h
  cG := z.cG
  geo := z.resGeoE h
  pins := z.pins_resRE h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

section Ex

variable (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')



set_option maxHeartbeats 2000000 in

theorem restrictOfExists_lift_scalar (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.restrictE e Wt' h hc).R.lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := z.restrictRealData_lift_scalar h i t

set_option maxHeartbeats 2000000 in

theorem restrictOfExists_error_tuples_twisted : (z.restrictE e Wt' h hc).R.err0 = z.R.err0 ∧ (z.restrictE e Wt' h hc).R.mu = z.resMu h ∧
    (z.restrictE e Wt' h hc).R.twPl = z.resTw Wt' := ⟨rfl, rfl, rfl⟩

theorem restrictE_R_of_thmB (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R = z.resR h := z.resRE_of_thmB h hB

set_option maxHeartbeats 2000000 in

theorem restrictE_kap (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R.kap = z.R.kap :=
  (Res.kapNew_of_thmB (z.resR h) (z.thmB_resR h hB)).trans (z.restrictRealData_constant_error h).1



set_option maxHeartbeats 4000000 in

theorem restrictE_holds (hH : Holds z.R z.F) : Holds (z.restrictE e Wt' h hc).R (z.restrictE e Wt' h hc).F := by
  rw [z.restrictE_R_of_thmB e h hc hH.prim.thmB]
  exact z.holds_resR h hH

set_option maxHeartbeats 4000000 in

theorem restrictE_inGeo_iff : GlobalTheory.RealGeo.InGeo (z.restrictE e Wt' h hc).geo ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  (Res.inGeo_geoScal_iff (z.resGeo h) (Res.kapNew (z.resR h)) (z.resR h).lam (z.resR h).err0).trans (z.inGeo_resGeo_iff h)

set_option maxHeartbeats 4000000 in

theorem restrictOfExists_nonzero_places : (z.restrictE e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate, mem_nonzero_index_places_iff_at_place_or_conjugate]
  have key : ∀ j v, NzAt ((z.resR h).updS (Res.kapNew (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔
      NzAt z.R z.F F0 j v := fun j v => (Res.nzAt_scal _ _ _ _ F0 j v).trans (z.nzAt_resR F0 h j v)
  exact exists_congr fun j => or_congr (key j _) (key j _)

end Ex


def restrictNonzeroOfExists (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) :=
  z.restrictE e (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)

section ExW

variable (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt)








end ExW

example (e : z.R.toRealDat.ExAt) : (z.restrictE e ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : Res.kapNew z.R = z.R.kap := Res.kapNew_of_scal z.R z.pins.char.scal.kap

example (hH : Holds z.R z.F) : (z.restrict hH ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : z.resTw Wt = z.R.twPl := Finset.ext fun v => (z.mem_resTw subset_rfl v).trans (z.mem_twPl v).symm

include z in

theorem conjStable : ConjStable X Wt := by
  intro w hw
  have ht := z.pins.char.tup
  rw [← z.plB_mem_twPl, plB_conj]
  by_contra hn
  exact ht.mu_ne _ ((z.plB_mem_twPl w).2 hw) ((ht.mu_conj _).symm.trans (ht.mu_off _ hn))

example (w : X.B.places.Pl) (j : Fin X.toD7.R.m) (h : F0 (plB X w) j ≠ 0) : w ∈ z.W1 F0 :=
  (z.mem_nonzero_index_places_iff_at_place_or_conjugate F0 w).2 ⟨j, Or.inl (Or.inr (Or.inr h))⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
