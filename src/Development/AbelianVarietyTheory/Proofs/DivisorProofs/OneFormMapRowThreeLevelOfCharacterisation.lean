import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedDataAllTuplesOfBaseTuple
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  first | exact @GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | exact GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | (intros; apply GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRow0 T R κ v₀ O i → GlobalTheory.OneMapAll.PinnedDataExist T R κ v₀ i → GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapAll.oneMapRowR_of_clauses | exact GlobalTheory.OneMapAll.oneMapRowR_of_clauses | (intros; apply GlobalTheory.OneMapAll.oneMapRowR_of_clauses <;> assumption)
end

section
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapAll

theorem identityRow_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio i Tp tup O _ hO
  obtain ⟨cc, -, u, -, -, -, h⟩ := GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Tp tup O hO
  exact ⟨u • cc, 1, h⟩

end GlobalTheory.OneMapAll
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOneMap_identity_every_normalised_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ i, GlobalTheory.OneMapAll.IdentityRow T R κ v₀ i := by
  atlas_forward_decl GlobalTheory.OneMapAll.identityRow_of_core
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → R.thP_vP → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧ O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧ O'.lev = (O i).lev := by
  first | exact @GlobalTheory.PinnedTuples.exists_pins_of_base | exact GlobalTheory.PinnedTuples.exists_pins_of_base | (intros; apply GlobalTheory.PinnedTuples.exists_pins_of_base <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tieIn_of_nonempty_tie :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ⟨fw⟩ => ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ := by
  atlas_forward_decl GlobalTheory.tieIn_of_nonempty_tie
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hR hoff hused hfw hio i hpins htie hspan
  have hin : TieIn T R κ v₀ := GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hfw
  refine GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span D G Pl0 T0 A T R κ v₀ O ph i hR.lev hR.grp.chiW hR.fam hR.models hpins htie
    (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hR hin hio O i hpins) (fun hG => ?_)
    (GlobalTheory.T.thetaOneMap_identity_every_normalised_family hCI D G Pl0 T0 A T R F κ v₀ hR hin hio i) hspan
  obtain ⟨O', h1, h2, -⟩ := GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple D G Pl0 T0 A T R κ v₀ O hR.lev hR.grp.chiW hR.fam hR.models hR.thP.vP hoff hused
    hfw i hpins hG
  exact ⟨O', h1, h2⟩

end GlobalTheory.OneMapCore
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  atlas_forward_decl GlobalTheory.OneMapCore.oneMapRowR_of_core
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core_of_size :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hoff hused hT hI i hP hph
  have hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have h0 : OneMapRow0 T R κ v₀ O i :=
    GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hci D G Pl0 T0 A T R F κ v₀ hC (GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hT) hI O i hP
  exact GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses hci D G Pl0 T0 A T R F κ v₀ O ph hC hoff hused hT hI i hP hph
    (GlobalTheory.T.classSums_span_cuspForms_baseTuple_second_field D G Pl0 T0 A T R F κ v₀ O hn hC hT hI i hP h0)

end GlobalTheory.OneMapCore
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  atlas_forward_decl GlobalTheory.OneMapCore.oneMapRowR_of_core_of_size
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRow3

theorem oneFormMapRow_threeLevel_of_characterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O ph hn hC hE hFW hIo i hP hT
  obtain ⟨hcore, hoff, hused⟩ := GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation D G Pl0 I0 T0 A3 T.Q.c.F R F hC hE
  exact GlobalTheory.T.oneMap_all_tuples_over_core_of_rankBound D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O ph hn hcore hoff hused hFW hIo i hP hT

end GlobalTheory.OneMapRow3
end
