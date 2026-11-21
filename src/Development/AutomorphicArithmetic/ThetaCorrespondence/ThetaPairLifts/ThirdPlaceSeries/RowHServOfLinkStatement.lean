import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeServiceGlobalReciprocity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReciprocityKernelServiceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReciprocityKernelService
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinkRStdTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHServOfKerServ

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Svd.LinkStd
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
theorem stdTie_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex)
    (h : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') {D : D7} {O : Obj D} {c : ℝ} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (e : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) : StdTie D O R.T.ker := by
  cases e
  exact StdTie.intro h.std
theorem linkR_stdTie_entry {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) Q (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) fun _ D O _ R => StdTie D O R.T.ker :=
  RowE.of_all fun _ _ _ _ R _ _ hl => by
    obtain ⟨q, R', h, e⟩ := hl
    exact _root_.GlobalTheory.Svd.LinkStd.stdTie_of_eq_alt q R' h R e
end GlobalTheory.Svd.LinkStd
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
namespace GlobalTheory.Svd
theorem servH_row_linkR_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    Row (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) (ServH (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) fun _ _ _ R => R.T.ker) := by
  intro hA hL p
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity hA (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) (fun _ _ _ R => R.T.ker)
    (fun K X f T c h => (GlobalTheory.Svd.builtC_hasPart p.s).2 K X f T c
      (IsBuiltE.isBuilt K X f T c (IsGoodE.isBuiltE K X f T c h)))
    (_root_.GlobalTheory.Svd.LinkStd.linkR_stdTie_entry p (IsGoodE p.s))
end GlobalTheory.Svd
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocity_kernel_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), Row (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p) (ServH (Bd := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) fun _ _ _ R => R.T.ker) := by
  atlas_forward_decl _root_.GlobalTheory.Svd.servH_row_linkR_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1
theorem row_hServ_of_kerServ_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (GlobalTheory.Svd.ServH fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => b.R.T.ker) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition Q Lk := by
  intro Q Lk h
  refine Row.imp h fun 𝒜 σ _ hs => ?_
  obtain ⟨⟨a, ha, hK⟩, hA⟩ := hs
  refine ⟨⟨a, ha, fun e he hle => ?_⟩, ⟨a, ha, fun e he hle => ?_⟩⟩
  · obtain ⟨K, hK⟩ := hK e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.Cp.d3_a hc) hL⟩
  · obtain ⟨K, _⟩ := hK e he hle
    exact ⟨K, fun Fm _ _ _ hc x hx _ i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i⟩
end GlobalTheory.Fc.R1
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory
theorem row_hServ_of_link_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) →
    _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  intro hA hL p Lk hLk
  have h1 := Row.map (Bd := _root_.GlobalTheory.Fc.BundleCondition) (Q := IsGoodE p.s) (Lk := Lk) (Bd' := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (Q' := IsGoodE p.s) (Lk' := _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p)
    (fun _ _ _ b => b.R) (fun _ _ _ _ _ h => h) (fun K β c b _ h => hLk K β c b h) (_root_.GlobalTheory.T.reciprocity_kernel_of_artin hA p)
  exact _root_.GlobalTheory.Fc.R1.row_hServ_of_kerServ_alt _ Lk h1
end GlobalTheory
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hServ_of_linkR : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  atlas_forward_decl _root_.GlobalTheory.row_hServ_of_link_alt
end
end
