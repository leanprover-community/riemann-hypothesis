import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeLogFormAbsLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndex

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.FlatSz
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.CovTop.FlatSz
namespace GlobalTheory.CovTop.FlatSz
theorem flatDegVal_covers_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ =>
    |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤
      9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by
  intro _
  have h1 := _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt
    (Q := fun Fm x _ ι _ _ _ PP => ∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)
    (fun _ _ _ _ _ _ C _ h _ _ _ => ⟨C, h⟩)
  have h2 := _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt
    (Q := fun _ _ _ _ p i _ PP => WtNum p i PP) _root_.GlobalTheory.CovTop.WtShape.wtN_z
    (fun _ _ _ _ _ _ _ _ h _ _ _ => h)
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_covers_of_imp (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt h1 h2)
    (fun _ _ _ _ p i _ _ h => abs_flatDegVal_le p i h.1.choose_spec h.2)
end GlobalTheory.CovTop.FlatSz
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_flatDegVal_logOm_le_nine_mul_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.FlatSz.flatDegVal_covers_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.CovSz
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem kapT_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ =>
    Real.log (CovTop.kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b := by
  intro _
  refine (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 18) _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i _ _ _ =>
    kapT_at p i (ha x hx ((le_max_left _ _).trans hle) ι p hp i) (hb x hx ((le_max_right _ _).trans hle) ι p hp i)⟩
end GlobalTheory.CovTop.CovSz
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_kap_le_and_lenT_mul_le_sqrt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.CovSz.kapT_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.ZedSz
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem zed_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 := by
  intro hS
  have hI := _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS
  have hHN := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  have hWN := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS hI) (Formalism.MainNotions.Closed.and hHN hWN)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨C1, -, a1, h1⟩, ⟨C2, -, a2, h2⟩⟩, ⟨C3, -, a3, h3⟩, ⟨C4, -, a4, h4⟩⟩ := hh
  refine ⟨0, le_rfl, max (max a1 a2) (max a3 a4), fun x hx hle ι p hp i hi Y _ => ?_⟩
  have e1 := h1 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle) ι p hp i
  have e2 := h2 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle) ι p hp i hi
  have e3 := h3 x hx (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle) ι p hp i
  have e4 := h4 x hx (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle) ι p hp i
  have key := zed_at p i (Fm.params x hx ι) (Fm.parT x hx ι) C3 1 C1 e1 e2.2.2.2.1 (fun τ => (e2.2.2.2.2.1 τ).1) e3 e4 hi
  have hb1 := e1.1
  have hbk := e1.2.2.2.2.2.1
  refine ⟨by linarith, ?_⟩
  by_contra hc
  push_neg at hc
  have : 1 / 2 * ((Fm.parT x hx ι).PP * kap p i) < _ * ((Fm.parT x hx ι).PP * kap p i) :=
    mul_lt_mul_of_pos_right hc (by linarith)
  linarith
end GlobalTheory.CovTop.ZedSz
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter_size_bounds' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.ZedSz.zed_size_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.WtSz
open GlobalTheory.CompHS
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
open GlobalTheory.CompHS
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
set_option maxHeartbeats 1000000 in
theorem wts_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧
      WtNum p i PP := by
    refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 10) _root_.GlobalTheory.CovTop.WtShape.wtN_z))
      fun Fm CH _ h => ?_
    obtain ⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩ := h
    exact ⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i =>
      ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩,
        ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
        ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i _ _ h hi _ _ =>
    at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2
end GlobalTheory.CovTop.WtSz
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_param_coeff_sum_bound' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.WtSz.wts_le_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
theorem wt_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => SizeAt p i PP C ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) ∧ WtNum p i PP := by
    refine (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) _root_.GlobalTheory.CovTop.WtShape.wtN_z)).imp
      fun Fm CH _ hh => ?_
    obtain ⟨⟨C, hC, a, ha⟩, ⟨C', -, b, hb⟩, ⟨C'', -, c, hc⟩⟩ := hh
    exact ⟨C, hC, max a (max b c), fun x hx hle ι p hp i =>
      ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i,
       ⟨C', hb x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
       hc x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i C _ h _ Y _ => by
    obtain ⟨h1, ⟨A, h2⟩, h3⟩ := h
    exact fun j hj => sum_abs_wt_le_point p i h1 h2 h3 hj
end GlobalTheory.CovTop.WtRun
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_param_coeff_sum_le_at_index' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.WtRun.wt_size_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.CovSz
theorem sizes_of_cover_alt : _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ zBase (Fm.L x ι) ^ 12 ≤ PP := by
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) ?_
  intro eps Fm x hx ι p i C _ hN hi Y hY
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hx1 := (Fm.L x ι).sc.one_lt_alt
  have he0 := (Fm.L x ι).sc.eps_pos
  have he1 := (Fm.L x ι).sc.eps_lt
  have hx16 : (16 : ℝ) ≤ (Fm.L x ι).sc.x := by
    have h1 : (Fm.L x ι).sc.L ≤ (Fm.L x ι).sc.x ^ ((1 : ℝ) / 52) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le he1.le
    have h2 : ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) = (Fm.L x ι).sc.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h3 : (10 : ℝ) ^ (52 : ℕ) ≤ ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (hL10.trans h1) _
    rw [h2] at h3
    linarith [show (16 : ℝ) ≤ 10 ^ (52 : ℕ) by norm_num]
  have hrec := fun j => GlobalTheory.sizes_record_at (Fm.L x ι) (Fm.sizes x hx ι) 5 (by norm_num) hx16 j
  obtain ⟨-, -, -, -, h100, hr5, -⟩ := hrec 0
  have hg : ∀ k, Real.exp (8 * (Fm.L x ι).sc.L) ≤ ((Fm.D x ι).host.g k : ℝ) := fun k => by
    have := (hrec k).1; unfold Formalism.BasicNotions.Scale.L; exact this
  have hgpos : ∀ k, (0 : ℝ) < ((Fm.D x ι).host.g k : ℝ) := fun k => lt_of_lt_of_le (Real.exp_pos _) (hg k)
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hf8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hN.f8
  have hfpos : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
  have hr2 : (2 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 2 ≤ (Fm.D x ι).R.r)
  refine ⟨p.fw.laws, ⟨by omega, by omega⟩, by linarith, ?_, ?_, hN.logfr.1, ?_, ?_, hN.f8, h100, hN.ppLow⟩
  ·
    have hM : Y.d.l₂.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 * 15 ^ expL (Fm.L x ι).sc.L := by
      rw [hY.1.lev.1.2.1, hY.1.pd]
      congr 1
      exact p.fw.laws.toLawsM.pins.2.1.1
    have he : (expL (Fm.L x ι).sc.L : ℝ) * Real.log 3 ≤ 3 * (Fm.L x ι).sc.L := by
      have := Nat.floor_le (show 0 ≤ 3 * (Fm.L x ι).sc.L / Real.log 3 by positivity)
      unfold expL
      rwa [le_div_iff₀ hlog3p] at this
    have h15 : Real.log 15 ≤ 5 / 2 * Real.log 3 := by
      have : Real.log ((15 : ℝ) ^ 2) ≤ Real.log ((3 : ℝ) ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have he0 : (0 : ℝ) ≤ expL (Fm.L x ι).sc.L := Nat.cast_nonneg _
    rw [hM]
    push_cast
    rw [Real.log_mul (mul_pos (hgpos 0) (hgpos 1)).ne' (by positivity : (0 : ℝ) < 15 ^ expL (Fm.L x ι).sc.L).ne',
      Real.log_mul (hgpos 0).ne' (hgpos 1).ne', Real.log_pow]
    have g0 := hN.logg 0
    have g1 := hN.logg 1
    nlinarith
  ·
    unfold fieldSz
    rw [hN.deg]
    have hd := hN.disc
    have h2f : Real.log ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤ (Fm.L x ι).sc.L := by
      refine le_trans ?_ hN.logfr.1
      push_cast
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hq : Real.log |(NumberField.discr (Fm.D x ι).host.E : ℝ)| / ((2 * (Fm.D x ι).R.f : ℕ) : ℝ) ≤
        2 * (Fm.L x ι).sc.L := by
      rw [div_le_iff₀ (by push_cast; positivity)]
      push_cast
      nlinarith
    linarith
  ·
    exact le_expL (by push_cast; nlinarith)
  · intro k
    have hA := hN.poly.1
    have hxA : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ C := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ C := Real.rpow_le_rpow_of_exponent_le hx1.le hA
    have hroom : ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) ≤ (Fm.L x ι).sc.b := by
      have := hN.room
      rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h6 : (Fm.L x ι).sc.x ^ (6 : ℕ) ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := pow_le_pow_left₀ (by linarith) hxA 6
    have h5 : (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 < (Fm.L x ι).sc.x ^ (6 : ℕ) := pow_five_add_one_lt hx16
    have hb : (Fm.L x ι).sc.b ≤ Real.exp (8 * (Fm.L x ι).sc.L) := by
      unfold Formalism.BasicNotions.Scale.b; exact Real.exp_le_exp.2 (by linarith)
    have hr5' : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) := by
      have e : (Fm.L x ι).sc.x ^ (5 : ℕ) = (Fm.L x ι).sc.x ^ (5 : ℝ) := by exact_mod_cast (Real.rpow_natCast _ 5).symm
      first | exact hr5 | (rw [e]; exact hr5)
    have : ((Fm.D x ι).R.r : ℝ) + 1 < (Fm.D x ι).host.g k :=
      calc ((Fm.D x ι).R.r : ℝ) + 1 ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 := add_le_add hr5' le_rfl
        _ < (Fm.L x ι).sc.x ^ (6 : ℕ) := h5
        _ ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := h6
        _ ≤ (Fm.L x ι).sc.b := hroom
        _ ≤ Real.exp (8 * (Fm.L x ι).sc.L) := hb
        _ ≤ (Fm.D x ι).host.g k := hg k
    exact_mod_cast this
theorem size_rows_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => LawsJ p.T ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ 1 ≤ (Fm.L x ι).sc.L ∧ Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L ∧ fieldSz (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ Real.log ((Fm.D x ι).R.f * (Fm.D x ι).R.r) ≤ (Fm.L x ι).sc.L ∧ 4 ≤ expL (Fm.L x ι).sc.L ∧ (∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k) ∧ 8 ≤ (Fm.D x ι).R.f ∧ 100 ≤ (Fm.D x ι).R.r ∧ |GlobalTheory.FlatLine.flatDegVal (dat p i) (Formalism.L2.DIV.ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 9 * (Fm.D x ι).R.r * (Fm.L x ι).sc.L ∧ Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ zBase (Fm.L x ι) ^ 12 ≤ PP ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ * (PP * kap p i) ≤ (Fm.L x ι).sc.b ∧ zed p i PP (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ ≤ 1 / 2 ∧ (∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1)) ∧ ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_covers_of_imp (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt _root_.GlobalTheory.CovTop.CovSz.sizes_of_cover_alt (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.abs_flatDegVal_logOm_le_nine_mul_of_size hS) (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.log_kap_le_and_lenT_mul_le_sqrt hS)
    (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.weight_parameter_size_bounds' hS) (_root_.GlobalTheory.CovTop.CovSz.covers_and_alt (_root_.GlobalTheory.T.weight_param_coeff_sum_bound' hS) (_root_.GlobalTheory.T.weight_param_coeff_sum_le_at_index' hS)))))) ?_
  intro eps Fm x hx ι p i Y PP h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a13⟩, b11, ⟨b12, b14⟩, ⟨b15, b16⟩, b17, b18⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, b11, b12, a13, b14, b15, b16, b17, b18⟩
end GlobalTheory.CovTop.CovSz
end
end
end
