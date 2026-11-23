module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IntertwinersExistScalarUpdateInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}



def geoR (z : Dat X I hX T Wt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) :
    GlobalTheory.RealGeo.GeoHalf z.core ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3).toRealDat fun _ => 1 :=
  ⟨(z.resGeo h).κ, (z.resGeo h).v₀,
    GlobalTheory.RealGeo.Upd.updFWT z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).fw,
    (z.resGeo h).bar,
    fun i => GlobalTheory.RealGeo.Upd.updO z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 ((z.resGeo h).O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).O i ((z.resGeo h).pins i),
    (z.resGeo h).rhoGeo, (z.resGeo h).equivAll, (z.resGeo h).cTie, (z.resGeo h).phase⟩



def res (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := (z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3
  cG := z.cG
  geo := geoR z Wt' h
  pins := pins_resK z h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set X.B.places.Pl} (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')



theorem res_exAt : (res z e Wt' h hc).R.toRealDat.ExAt := intertwinersExist_scalar_update_invariant (exAt_res z h e) _ _



theorem res_inGeo (hi : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (res z e Wt' h hc).geo := by
  have h' := (z.inGeo_resGeo_iff h).2 hi
  exact ⟨h'.jEvExists, h'.jEvBar, h'.evInj, h'.jUnif, h'.geoAct, h'.latFull, h'.dimMatch⟩



theorem restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces (F0) : (res z e Wt' h hc).W1 F0 = z.W1 F0 := by
  let z' := res z e Wt' h hc
  exact Set.ext fun v =>
    (z'.mem_nonzero_index_places_iff_at_place_or_conjugate F0 v).trans
      ((nz_updS (z.resR h) z'.F (kapOf (z.resR h)) (z.resR h).lam3 F0 (plB X v)).trans
        ((exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _)).trans
          (z.mem_nonzero_index_places_iff_at_place_or_conjugate F0 v).symm))



theorem res_std (hs : z.Std) : (res z e Wt' h hc).Std := by
  obtain ⟨⟨c, h1, h2, h5⟩, hV⟩ := hs
  refine ⟨⟨c, h1, fun hc' t φ g x hm => h2 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h5⟩, fun i => ?_⟩
  obtain ⟨cv, h3, h4, h6⟩ := hV i
  exact ⟨cv, h3, fun hc' t φ g x hm => h4 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h6⟩

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem of_diag {n : ℕ} {P : Fin n → Fin n → Prop} (H : ∀ i, P i i) (i i' : Fin n) (h : (i : ℕ) = i') : P i i' :=
  (Fin.ext h : i = i') ▸ H i



theorem res_ext (z : Dat (w.st Z) w.I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set B.places.Pl} (h : Wt' ⊆ Wt)
    (hc : ConjStable (w.st Z) Wt') : Ext z (res z e Wt' h hc) := by
  exact {
    H := HEq.rfl
    l := HEq.rfl
    c := HEq.rfl
    Dw := HEq.rfl
    Xo := HEq.rfl
    U := HEq.rfl
    V := HEq.rfl
    dict := HEq.rfl
    mu := HEq.rfl
    Kf := HEq.rfl
    cE := HEq.rfl
    chiW := HEq.rfl
    x₀ := HEq.rfl
    iota := HEq.rfl
    ψ := HEq.rfl
    θ := HEq.rfl
    βW := HEq.rfl
    βY := HEq.rfl
    nW := HEq.rfl
    βV := HEq.rfl
    ΛV := HEq.rfl
    ΛW := HEq.rfl
    Pg := HEq.rfl
    eG := HEq.rfl
    Sb := HEq.rfl
    BV := of_diag fun _ => ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    MW := by
      refine of_diag fun i => ?_
      refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun φ φ' hφ => ?_⟩
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
      subst h2
      exact HEq.rfl
    forms := by
      refine of_diag fun i => ?_
      intro φ φ' hφ k k' hk
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
      subst h2
      have hN : (type_of% k') = (type_of% k) := rfl
      have hnn : (res z e Wt' h hc).R.nW i = z.R.nW i := rfl
      have h3 : cast hN k' = k := (cast_eq_iff_heq).2 ((Fin.heq_ext_iff hnn).2 hk.symm)
      subst h3
      rfl
    W1 v v' hv := by
      have e' : v = v' := (w.D Z).plEq.injective (HeightOneSpectrum.ext (Ideal.ext fun x => hv x x rfl))
      exact e' ▸ (Set.ext_iff.mp
        (restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces z e h hc (fun _ _ => 0)).symm v)
    cV := of_diag fun _ => ⟨HEq.rfl, HEq.rfl⟩
    pb := HEq.rfl
    ΛY := (HEq.refl z.R.ΛY)
    κ := by
      refine of_diag fun i => ⟨?_, ?_, ?_⟩
      · exact (HEq.refl (z.geo.κ i).aP)
      · exact (HEq.refl (z.geo.κ i).aM)
      · exact (Eq.refl (z.geo.κ i).n)
    ref := by
      refine of_diag fun i => ?_
      let μ := mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (HEq.refl (z.R.vP i μ))
      · exact (HEq.refl (z.R.HV i μ))
      · exact (HEq.refl (z.R.thF i μ))
      · exact (HEq.refl (z.R.thG i μ))
      · exact (HEq.refl (z.R.νV i μ))
      · exact (HEq.refl (z.R.fdV i μ))
      · exact (HEq.refl (z.R.νW i))
      · exact (HEq.refl (z.R.fdW i))
    jL := by
      refine of_diag fun i => ?_
      intro ok ok' φ φ' hφ
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := Subtype.ext (funext fun d => Subtype.ext
        (MvPolynomial.map_injective _ (RingHom.injective _) (eq_of_heq (hφ d d HEq.rfl))))
      subst h2
      exact (by with_unfolding_all exact (HEq.refl (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok (cast hT φ') :)))) :))
  }

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.Rw

theorem stepW_keep_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)



theorem exists_pre2_of_fine_of_resChar_mem : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.CuspRapidDecay → WeightCaseCondition → StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G → GrpTrue Z.N f → GrpAt (w.st Z) w.I →
      DV.KapDef (w.D Z) → Fine z → (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) →
      (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) →
      ∃ P : Pre2 K w, P.Z₀ = Z ∧ P.Wt = z.W1 (F0K K.s (w.D Z)) ∧ Ext z P.z := by
  intro hWe hDS hHC hCR hHW
  have hInp := GlobalTheory.LinksInputs.inputs_of_hypotheses hWe hDS hHC hCR
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hAll := hId.and (hHW.and (stepW_keep_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start))
  refine hAll.trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨-, -, hCoh⟩, hHW', hHost⟩ := H
  intro Z hX z hG2 hGT hGA hKap hFine hsub hSp
  obtain ⟨hEx, hGeo, hCore, hStd⟩ := hFine
  let F0 := F0K K.s (w.D Z)
  let W := z.W1 F0
  have hle : W ⊆ {v | B.places.resChar v ∈ T.pl} := hsub
  have hc : ConjStable (w.st Z) W := z.nonzero_index_places_conj_stable F0
  let z' := ResStd.res z hEx W hle hc
  have hW : z'.W1 F0 = W := ResStd.restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces z hEx hle hc F0
  have hEx' : z'.R.toRealDat.ExAt := ResStd.res_exAt z hEx hle hc
  have hGeo' : GlobalTheory.RealGeo.InGeo z'.geo := ResStd.res_inGeo z hEx hle hc hGeo
  have hCore' : CoreP z' := hCore
  have hStd' : z'.Std := ResStd.res_std z hEx hle hc hStd
  have hH : Holds z'.R z'.F := hHW' Z hX W z' hGT hGA hKap hEx' hGeo' hCore' hG2 hW.symm hsub
  have hcs (v : B.places.Pl) : B.places.conj v ∈ W ↔ v ∈ W :=
    ⟨fun hv => (B.places.conj_conj v) ▸ hc (B.places.conj v) hv, hc v⟩
  obtain ⟨-, hFmax, -, -, hSt, -⟩ := hHost (w.st Z) hO
  have hRows : Nonempty (RowPk w z') :=
    GlobalTheory.T.nonempty_rowLiftFamily_over_columnChoices B f T w Z hX W z' (hInp (w.D Z))
      hFmax (hSt 0).1 (fun i => (hSt ((i : ℕ) + 1)).2.2 (Nat.zero_lt_succ _) i.2) hH hcs
  refine hRows.elim fun q => ?_
  exact ⟨{
    Z₀ := Z
    hX := hX
    Wt := W
    z := z'
    q := q
    g := hG2
    coh := hCoh
    grp := hGT
    grpAt := hGA
    kap := hKap
    intersectionNumber_baseChange := hH
    exAt := hEx'
    inGeo := hGeo'
    core := hCore'
    exact := hW.symm
    sub := hsub
    supp := hSp
    std := hStd' }, rfl, rfl, ResStd.res_ext z hEx hle hc⟩

end GlobalTheory.Mem.R3.Rw

end
