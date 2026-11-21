import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GaloisRepDescendsAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInputsAllStates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyTiedAllStates
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FitsOL
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsParamsAtMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XiHTupTThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesWithLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadThirdLocalOfCoeff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PinOfNTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointCondThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Auxiliary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParametersParametersNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLaws

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdFits
theorem third_component_fits_integral_lattice_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → (GlobalTheory.HeightCounting.Fin3.oL x L).Fits :=
  fun _ _ _ => GlobalTheory.Mem.Top.Bl.StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ _ L _ _ => GlobalTheory.HeightCounting.Fin3.fitsL (x := x) L
end GlobalTheory.HeightCounting.Up.ThirdFits
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdTied
theorem third_component_hecke_character_tuple_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ μ, Formalism.IndefR.RecTie.Used0 (withLoc L) μ → m.z.R.toLevCh.xiH (r.Y.tupT μ) = (tpL L l.c.tp).xi μ := by
  intro hL hP hX
  refine StepW.of_all fun K B f T w _ _ _ P x => ?_
  intro l big L _ _ m _ _ s r _ μ hμ
  refine (m.z.lev.xiH (r.Y.tupT μ)).trans ?_
  have b := r.Y.tupTie μ hμ
  rw [r.tup, m.tup] at b
  rw [b]
  exact (congrFun l.c.xi_eq μ).symm
end GlobalTheory.HeightCounting.Up.ThirdTied
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Fin
theorem finite_types_with_local_conditions_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ {o : P.q.Over} (m : Moved o), m.Copy → m.Coh → ∀ (s : Side0 o) (r : ReadPk m s), r.Pin → TypesTrue (withLoc L).ntypes m.z.R.C.P m.z.R.C.W := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ o m _ _ s r _
  rw [m.z.lev.C, w.C_eq]
  have hg : TypesTrue x.o.N.ntypes f.P f.W := x.fits.grp
  exact ⟨fun k v => hg.pl k v, fun k => hg.teich k, fun k v j => hg.chi k v j, fun k p => hg.ser k p⟩
end GlobalTheory.HeightCounting.Fin
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ThirdIdx
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Rows
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
end GlobalTheory.HeightCounting.Up.ThirdIdx
namespace GlobalTheory.HeightCounting.Up.ThirdIdx
theorem exists_divisor_eigen_index_third_component_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∃ (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd), Nonempty (E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m _ _ s r _
  letI : Algebra (↥m.z.core.Q.c.F) (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.what₂.LL := m.z.alg
  have hX : Nonempty (DivX (GlobalTheory.HeightCounting.Fin3.DL x L)) := nonempty_divX (Y := r.Y) r.Z m.z.pins m.intersectionNumber_baseChange
  rw [GlobalTheory.HeightCounting.Fin3.DL_eq] at hX
  obtain ⟨Xd⟩ := hX
  obtain ⟨c⟩ := nonempty_ix m.intersectionNumber_baseChange
  exact ⟨Xd, GlobalTheory.eigIdxFiniteTypes _ _, ⟨fun _ => c⟩⟩
end GlobalTheory.HeightCounting.Up.ThirdIdx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_index_divisibility_of_cmDatum_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∃ (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd), Nonempty (E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divisor_eigen_index_third_component_alt | exact _root_.GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divisor_eigen_index_third_component_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divisor_eigen_index_third_component_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ThirdAgree
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Gen
section Copy
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}
end Copy
section Main
set_option maxHeartbeats 4000000 in
theorem third_components_agree_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf (rep : (withLoc L).what₂.FT → NG.FinTyp (withLoc L).host.E (withLoc L).R.r), HEq rep (repOf x.r.Y) → Nonempty (GlobalTheory.NJoin.Agree (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) (mtL L l.mt.M) rep) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m hcp hco s r hpin hC Xd E labPi hb htup hg hf rep hrep
  have c1 := cV_copy (B := B) (C := w.C) (a := P.Z₀) (GlobalTheory.HeightCounting.Fin3.oL x L).Z P.z m.z m.Xg m.tr ((by with_unfolding_all exact (hcp.core :))) ((by with_unfolding_all exact (hcp.R :)))
  have c0 := cV_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :)))
  have ecV := cV_two (a := P.Z₀) x.o.Z (GlobalTheory.HeightCounting.Fin3.oL x L).Z c0 c1
  have hJ : HEq m.t.lf.jMt x.m.t.lf.jMt := hco.jMt.trans x.coh.jMt.symm
  have kJ : ∀ μ (i : Fin (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.R.m) y,
      HEq (m.t.lf.jMt μ i y) (x.m.t.lf.jMt ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) := fun μ i y => (by with_unfolding_all exact ((heq_apply (D := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7) (Mt := fun μ j => (P.q.p.sL μ j).A) ecV
      ((m.t.lf.jMt)) ((x.m.t.lf.jMt)) ((hJ)) μ i y) : _))
  have eR1 : m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq hco.rep) :))
  have eR0 : x.m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq x.coh.rep) :))
  have eRep : rep = (by with_unfolding_all exact ((repOf x.r.Y) :)) := (by with_unfolding_all exact ((eq_of_heq hrep) :))
  have hrep' : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)) := by
    intro σ
    have a1 : (rep σ).Iso ((by with_unfolding_all exact ((repOf x.r.Y σ) :))) := (by with_unfolding_all exact ((iso_of_eq (congrFun eRep σ)) :))
    have a2 := x.pin.rep ((by with_unfolding_all exact (σ :)))
    have a3 : ((by with_unfolding_all exact ((x.m.t.rep σ) :)) : NG.FinTyp (withLoc L).host.E (withLoc L).R.r).Iso ((by with_unfolding_all exact ((m.t.rep σ) :))) := (by with_unfolding_all exact ((iso_of_eq ((congrFun eR0 σ).trans (congrFun eR1 σ).symm)) :))
    have a4 := NG.IsoRep.symm (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)).stable (hpin.rep σ)
    exact (by with_unfolding_all exact ((NG.IsoRep.trans a1 (NG.IsoRep.trans a2 (NG.IsoRep.trans a3 a4))) :))
  let DL := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7
  let jm : ∀ μ, Used0 DL μ → ∀ i : Fin DL.R.m, DL.what₂.Mt μ (i.1 + 1) → GA DL (Vc DL i) →
      (cpV (GlobalTheory.HeightCounting.Fin3.oL x L).Z x.m.z.R.cV i).W :=
    fun μ h i y => (by with_unfolding_all exact ((x.r.Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))
  have hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (jm μ h i y) := fun μ h i y => (by with_unfolding_all exact (((hpin.jMt μ h i y).trans ((kJ μ i y).trans (x.pin.jMt μ h i y).symm)) :))
  exact (by with_unfolding_all exact ((agree_of_data (D := DL) (R := m.z.R) (F := m.z.F) r.Y (cf := ((cfL L (cfOf x)))) (nch := ((chL L l.c.ch)))
    (((tpL L l.c.tp))) ((hC)) ((Xd)) ((E)) ((labPi)) ((hb)) ((htup)) ((hg)) ((hf)) (((mtL L l.mt.M))) ((rep))
    ((hrep')) _ ecV (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) ((l.mt.ad.std)) ((l.mt.ad.eW)) jm hj ((l.mt.ad.read)) ((l.mt.ad.rat))
    ((l.mt.ad.wt))) : _))
end Main
end GlobalTheory.HeightCounting.Up.ThirdAgree
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
namespace GlobalTheory.HeightCounting.Up.ThirdTied
theorem ordinary_idempotent_third_component_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m _ _ s r _ hC Xd E labPi hb htup hg hf
  exact GlobalTheory.HeightCounting.Up.IdempotentAdelicReading.goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ m.intersectionNumber_baseChange.ok.ok2
end GlobalTheory.HeightCounting.Up.ThirdTied
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt | exact _root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
set_option maxHeartbeats 4000000 in
theorem third_place_fixed_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.cf = cfL L (cfOf x) ∧ Q.C = chL L l.c.ch ∧ HEq Q.tp (tpL L l.c.tp) ∧
      HEq Q.rep (repOf x.r.Y) ∧ HEq Q.M (mtL L l.mt.M) := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, h1, h2, h3, h4, h5⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
open GlobalTheory.HeightCounting.Fin3 GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 4000000 in
theorem readCoefField_eq_cfL_of_moved_copy_coherent : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → m.z.R.C = cfL L (cfOf x) := by
  intro hL _ _
  exact StepW.of_all fun K B f T w _ _ _ P x l big L hB hO m _ _ s r _ => m.z.lev.C
set_option maxHeartbeats 4000000 in
theorem third_place_linked_data_exists : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  intro hL hP hX
  have H := ((_root_.GlobalTheory.HeightCounting.Up.ThirdFits.third_component_fits_integral_lattice_alt hL hP hX).and (GlobalTheory.HeightCounting.Up.GapAllStates.gapR_allSt)).and (_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt.2.and ((_root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.readCoefField_eq_cfL_of_moved_copy_coherent hL hP hX).and
    ((_root_.GlobalTheory.HeightCounting.Up.ThirdTied.third_component_hecke_character_tuple_alt hL hP hX).and ((_root_.GlobalTheory.HeightCounting.Fin.finite_types_with_local_conditions_alt hL hP hX).and ((_root_.GlobalTheory.T.eigen_index_divisibility_of_cmDatum_alt hL hP hX).and
    ((_root_.GlobalTheory.HeightCounting.Up.ThirdAgree.third_components_agree_alt hL hP hX).and (_root_.GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt hL hP hX)))))))
  refine H.trans (StepW.of_all fun K B f T w _ _ h P x l => ?_)
  obtain ⟨⟨hfits, hgap⟩, hpar, hcf, htp, hty, hidx, hag, he0⟩ := h
  refine ⟨fun _ => ∅, fun L hB hO => ?_⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_fixed_alt hL hP x l _ L hB
  obtain ⟨x', hx'⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hX.weil hX.ds hP.hc hP.decay K B f T w P (oL x L) (hfits P x l _ L hB hO) x.G_eq
    x.etaF (bkL L)
  obtain ⟨o, fits', G_eq', etaF', bk', m, cp, co, s, r, pn⟩ := x'
  dsimp only at hx'
  subst hx'
  have hC := hcf P x l _ L hB hO m cp co s r pn
  have ht := htp P x l _ L hB hO m cp co s r pn
  have hT := hty P x l _ L hB hO m cp co s r pn
  obtain ⟨Xd, E, ⟨labPi⟩⟩ := hidx P x l _ L hB hO m cp co s r pn
  have hg : GlobalTheory.LiftRows.Given m.z.R.toRealDat m.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak m.z.R m.z.F m.z.pins.char m.exAt).1, (hpar P x).2 L, m.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ m.z.pins.char.base.lev hT, m.z.pins.keep.guard, hgap P x⟩
  obtain ⟨ag⟩ := hag P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP Q.rep h4
  have e0 := he0 P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP
  obtain ⟨T0, -, -⟩ := _root_.GlobalTheory.HeightCounting.Up.RealOfReading.exists_linked_data_of_agreement Q (realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi
    m.z.pins.char.base ht hg m.z.pins.char.fullP) h1 h2 h3 (eq_of_heq h5) HEq.rfl ag e0
  exact ⟨T0⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_system_third_place_linked_data : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists | exact _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists | (intros; apply _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.JointConditionThird
theorem upper_ramification_joint_condition_third_jump_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalDatumCompatibility D' := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  refine GlobalTheory.DesignBC.jointCond_of_definite _ fun j h1 h2 => ?_
  have h := (w.st x.o.Z).B.toPre.V_posDef j h1 h2
  intro τ
  exact Or.inl (h τ)
end GlobalTheory.HeightCounting.Up.JointConditionThird
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem upper_ramification_third_jump_holds_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  intro hL hP
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  let A' : _root_.GlobalTheory.HeightCounting.AUSideAlt (withLoc L) := { l.a.A.au with }
  have cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T' := { l.a.cg with }
  have au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL (withLoc L) T' A' := fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h
  exact _root_.UpperTheory.BaseChangeIdentities.Conclusion1_alt_alt_alt hP.bc hP.what₂.bern hP.gen hP.std hL (withLoc L) T' A' cg au
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.third_member_upper_ramification' : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | exact _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.upper_ramification_third_jump_holds_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameters_parameterChoice_nonempty : (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧ ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | exact _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.HeightCounting.Up.RowsAtStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 2000000 in
theorem adm8_and_lamUsed_of_rational_reading_and_parameters : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → OverRows fun _ _ _ _ w Z _ _ z p0 Y => RationalReadingWithoutCongruence z.R z.F p0 Y →
    (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  intro hN hPX
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo hEx _ hGrp _ hRd hp
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    rw [z.lev.C, w.C_eq]
    exact hGrp
  have hME := _root_.GlobalTheory.T.twisted_multiplicity_one hPX.ana hPX.dsc hN.decay hN.hc hPX.trc hPX.dm hPX.flath hN.zel
    hN.what₂.geo hN.greenC z.R z.F hHo.ok z.pins.char hEx hH hp B.ccK_top z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev hT)
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  have h0 := GlobalTheory.T.positive_scalars_without_congruence_lengths hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH
  exact ⟨h0.1 hIR, h0.2⟩
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000 in
theorem adm8_and_lamUsed_all_states_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x =>
    SumRepresentations.adm8 (Dof x) ∧ GlobalTheory.NRows.LamUsed (Dof x) := by
  intro hN hPX
  have h1 := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (_root_.GlobalTheory.HeightCounting.Up.RowsAtStates.adm8_and_lamUsed_of_rational_reading_and_parameters hN hPX)
  have h2 := _root_.GlobalTheory.T.exists_parameters_parameterChoice_nonempty.2
  refine (StepW.and h1 h2).trans (StepW.of_all fun K B f T w _ _ hh P x => ?_)
  obtain ⟨hA, hB⟩ := hh
  exact hA P x x.r.Z (hB P x).1
end GlobalTheory.HeightCounting.Up.RowsAtStates
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => SumRepresentations.adm8 (Dof x) ∧ GlobalTheory.NRows.LamUsed (Dof x) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.RowsAtStates.adm8_and_lamUsed_all_states_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.RowsAtStates.adm8_and_lamUsed_all_states_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.RowsAtStates.adm8_and_lamUsed_all_states_of_published_inputs <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem cenLoc_third_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) : CenLoc (withLoc Lc) (mtL Lc l.mt.M) := by
  intro i
  have h := cen_twisted x.r.Y x.m.z.cG x.m.z.pins.char.base x.m.z.pins.keep x.m.intersectionNumber_baseChange.ok.ok2 (cenRead_state x) l.mt.M l.mt.ad l.mt.mt
    ((withLoc Lc).nd.w i) ((withLoc Lc).nd.w_tw i) ((withLoc Lc).nd.mu i) ((withLoc Lc).nd.mu_w i) ((withLoc Lc).nd.j i)
    ((withLoc Lc).nd.j_range i).1 ((withLoc Lc).nd.j_range i).2
  exact (by with_unfolding_all exact (h :))
set_option maxHeartbeats 2000000 in
theorem tame_coupled_with_loc {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) :
    ∀ k v, ∃ κ : IsLocalRing.ResidueField ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar ((withLoc Lc).host.g k),
      Formalism.L2.NT.TameCoupled ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) κ ((withLoc Lc).ntypes.tg k v)
        (GlobalTheory.Mem.TypePl.labDat ((withLoc Lc).host.g k)).gen :=
  fun k v => ⟨l.a.A.grp.kv k v, by
    have h := l.a.A.grp.tg_tame k v
    rw [l.a.zeta k] at h
    exact h⟩
end GlobalTheory.SerThird
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem exists_character_choice_with_loc_of_built (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.M = mtL L l.mt.M := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, -, -, -, -, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, eq_of_heq h5⟩
set_option maxHeartbeats 4000000 in
theorem locComp_of_isRc_classMapD_cenLoc : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x =>
    ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  intro hL hP
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l
  refine ⟨fun _ => ∅, fun Lc hB _ => ?_⟩
  obtain ⟨Pn, hM⟩ := _root_.GlobalTheory.SerThird.exists_character_choice_with_loc_of_built hL hP x l _ Lc hB
  exact _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty_explicit hP.what₂ hP.green hP.zel hL (withLoc Lc) Pn _ (labTie_withLoc x Lc) (_root_.GlobalTheory.SerThird.tame_coupled_with_loc x l Lc)
    (hM ▸ _root_.GlobalTheory.SerThird.cenLoc_third_alt x l Lc)
end GlobalTheory.SerThird
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ser_loc_eventually_of_built : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  first | exact @_root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerThird.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PtInputsX
theorem inputs_at_third_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility →
    AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') := by
  intro hL hP hX
  have h := (((_root_.GlobalTheory.T.compatible_system_third_place_linked_data hL hP hX).and (_root_.GlobalTheory.HeightCounting.Up.JointConditionThird.upper_ramification_joint_condition_third_jump_alt hL hP)).and
    (_root_.GlobalTheory.T.third_member_upper_ramification' hL hP)).and ((_root_.GlobalTheory.T.adm8_and_lamUsed_of_geometric_galois_compat hP hX).and (_root_.GlobalTheory.T.ser_loc_eventually_of_built hL hP))
  refine h.trans (StepW.of_all fun K B f T w _ _ hh P x l => ?_)
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h45, h6⟩ := hh
  have h4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.NRows.LamUsed D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).2⟩
  have h5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SumRepresentations.adm8 D' :=
    ⟨fun _ => ∅, fun _ _ _ => (h45 P x).1⟩
  have e := fun (P₁ P₂ : D7 → Prop) => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt _ _ _ l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have a := (e _ _).1 (h1 P x l) ((e _ _).1 (h2 P x l) ((e _ _).1 (h3 P x l) ((e _ _).1 h4
    ((e _ _).1 h5 (h6 P x l)))))
  refine (e _ _).2.1 (fun D' hD' hO => ?_) a
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hD'
  obtain ⟨T⟩ := t1 hO
  exact ⟨⟨T, ⟨hO, t2 hO, t3 hO, t4 hO, t5 hO, t6 hO,
    _root_.GlobalTheory.T.galoisRep_descends_at_real_places hP.decay hP.howe hX D' T.P.cf T.P.C T.P.tp T.X⟩⟩⟩
end GlobalTheory.PtInputsX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nonempty_inputs_of_level_c : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedInputs hL D') := by
  first | exact @_root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt | exact _root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt | (intros; apply _root_.GlobalTheory.PtInputsX.inputs_at_third_place_alt <;> assumption)
end
end
end
