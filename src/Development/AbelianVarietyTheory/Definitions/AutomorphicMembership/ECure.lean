import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def reTR {X : HidaSetting D} (T : TypedRed X) : TypedRed (reX Z X) := { T with }

set_option maxHeartbeats 4000000 in

def reCS {X : HidaSetting D} {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X u what₂) :
    ColSys (reX Z X) u what₂ := { c with }

set_option maxHeartbeats 4000000 in

def eHHre (X : HidaSetting D) : HHX X ≃ₗᵢ[ℂ] HHX (reX Z X) := LinearIsometryEquiv.refl ℂ (HHX X)

end GlobalTheory.Mem.SRe

end
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) : Transport (reX Z X) u F' where
  wt := T.wt
  wt_isom := T.wt_isom
  wt_e := T.wt_e
  wt_f := T.wt_f
  weight_z := T.weight_z
  ιA := T.ιA
  ιA_rat := T.ιA_rat
  ιA_int := T.ιA_int
  h0 := T.h0
  hc := T.hc
  hc_rep := fun c => by rw [hy]; exact T.hc_rep c
  J := T.J
  J_eqv := T.J_eqv
  J_val := T.J_val
  J_isom := fun c ξ η => by rw [he]; exact T.J_isom c ξ η

set_option maxHeartbeats 4000000 in

theorem colDictL_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (hK : X.LevelSubgroupCharacter) (x : Cu X u hK) :
    colDictL (reX Z X) (reTr Z T hy he) hK x = colDictL X T hK x := by
  funext c z
  show T.J (shP X u x.1 (T.hc c)) (F'.val0.eY z) = T.J (shP X u x.1 (T.hc c)) (F.val0.eY z)
  rw [he]
  rfl

end GlobalTheory.Mem.SRe

end
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option smartUnfolding false in
set_option maxHeartbeats 4000000 in

def reY {X : HidaSetting D} (Y : Full X) : Full (reX Z X) where
  hK := (Y.hK)
  TR := (reTR Z Y.TR)
  psi_ne := (Y.psi_ne)
  what₂ := (Y.what₂)
  rowsOK := (Y.rowsOK)
  split := (Y.split)
  cs := (fun (u : @Formalism.BasicNotions.Rows.Data.Word (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D)) ↦ @GlobalTheory.Mem.SRe.reCS D Z X u (@Formalism.L2.SG.Full.Full.what₂ D X Y u) (@Formalism.L2.SG.Full.Full.cs D X Y u))
  colReps := (Y.colReps)
  Dt := (Y.Dt)
  reps := (Y.reps)
  FN := (Y.FN)
  FN_fund := (Y.FN_fund)
  δ := (Y.δ)
  M := (Y.M)
  agree := (Y.agree)
  δ_pin := (Y.δ_pin)

set_option maxHeartbeats 4000000 in

def eRT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : RT Y u u' ≃ RT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)

set_option maxHeartbeats 4000000 in

def eTT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : TT Y u u' ≃ TT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)

set_option maxHeartbeats 4000000 in

def eCure {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y)) (u : D.what₂.Word) :
    ColT (h.shInj u) ≃ₗᵢ[ℂ] ColT (h'.shInj (wd Z u)) := by kexactB LinearIsometryEquiv.refl ℂ (ColT (h.shInj u))

end GlobalTheory.Mem.SRe

end
end
