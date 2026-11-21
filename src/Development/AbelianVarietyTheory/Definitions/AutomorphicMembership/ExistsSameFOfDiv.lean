import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices

section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def reG {X : HidaSetting D} (G : GoodOp X) : GoodOp (reX Z X) where
  Rg := (G.Rg)
  Rg_spec := (G.Rg_spec)

set_option maxHeartbeats 4000000 in

def eEECre {X : HidaSetting D} (G : GoodOp X) : EEC X G ≃ₗᵢ[ℂ] EEC (reX Z X) (reG Z G) := (LinearIsometryEquiv.refl ℂ ↥(EEC X G))

set_option maxHeartbeats 4000000 in

theorem measTie_reX {X : HidaSetting D} {hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I} (h : X.MeasTie hb) :
    (reX Z X).MeasTie hb := (h)

set_option maxHeartbeats 4000000 in

theorem measCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ}
    (h : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ) : Formalism.L2.SG.MassDataConc.MeasCompatψ (reX Z X) ψ := (h)

set_option maxHeartbeats 4000000 in

theorem locCompat_reX {X : HidaSetting D} {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ} {w : D.what₂.Word}
    (h : Formalism.L2.SG.LocVol.LocCompatX X ψ w) : Formalism.L2.SG.LocVol.LocCompatX (reX Z X) ψ (wd Z w) := (h)

theorem colDict_congr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} (T : Transport X u F) (hK : X.LevelSubgroupCharacter)
    (L : Cu X u hK →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) (hL : ∀ x, L x = colDictL X T hK x) :
    (ColDictInto X T hK → ∀ x, L x ∈ (D.mem u).A.Mu0) ∧
    (ColDictBij X T hK → Function.Injective L ∧ ∀ φ ∈ (D.mem u).A.Mu0, ∃ x, L x = φ) ∧
    ∀ {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (hinj : Function.Injective (sharp hK cs)),
      ColDictIsom X T hK cs hinj → ∀ x y : ColT hinj, inner ℂ x y = (D.fm u).ipC 0 (L (toCu X hK x)) (L (toCu X hK y)) := by
  obtain rfl : L = colDictL X T hK := LinearMap.ext hL
  exact ⟨fun h => h, fun h => h, fun _ _ h => h⟩

section Col

set_option maxHeartbeats 4000000

variable {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)

set_option maxHeartbeats 4000000 in

theorem colDictInto_reTr (h : ColDictInto X T Y.hK) : ColDictInto (reX Z X) (reTr Z T hy he) (reY Z Y).hK := (by with_unfolding_all exact ((colDict_congr T Y.hK ((by with_unfolding_all exact (colDictL (reX Z X) (reTr Z T hy he) (reY Z Y).hK :)))
    ((by with_unfolding_all exact (colDictL_reTr Z T hy he Y.hK :)))).1 h :))

set_option maxHeartbeats 4000000 in

theorem colDictBij_reTr (h : ColDictBij X T Y.hK) : ColDictBij (reX Z X) (reTr Z T hy he) (reY Z Y).hK := (by with_unfolding_all exact ((colDict_congr T Y.hK ((by with_unfolding_all exact (colDictL (reX Z X) (reTr Z T hy he) (reY Z Y).hK :)))
    ((by with_unfolding_all exact (colDictL_reTr Z T hy he Y.hK :)))).2.1 h :))

set_option maxHeartbeats 4000000 in

theorem colDictIsom_reTr (hF : FinX Y) (hF' : FinX (reY Z Y)) (h : ColDictIsom X T Y.hK (Y.cs u) (hF.shInj u)) :
    ColDictIsom (reX Z X) (reTr Z T hy he) (reY Z Y).hK ((reY Z Y).cs u) (hF'.shInj u) := (by with_unfolding_all exact ((colDict_congr T Y.hK ((by with_unfolding_all exact (colDictL (reX Z X) (reTr Z T hy he) (reY Z Y).hK :)))
    ((by with_unfolding_all exact (colDictL_reTr Z T hy he Y.hK :)))).2.2 (Y.cs u) (hF.shInj u) h :))

end Col

set_option maxHeartbeats 4000000 in

theorem levelMatch_reTr {X : HidaSetting D} {u : D.what₂.Word} {F : Forms0 D u} {F' : Forms0 (reD D Z) u} (T : Transport X u F)
    (hl : F'.cls0.lev = F.cls0.lev) (hy : F'.cls0.y = F.cls0.y) (he : F'.val0.eY = F.val0.eY) (Y : Full X)
    (h : LevelMatch X T Y.hK) : LevelMatch (reX Z X) (reTr Z T hy he) (reY Z Y).hK := by
  unfold LevelMatch
  rw [hl]
  exact (h)

end GlobalTheory.Mem.SRe

end
end

section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000

def SPack.re {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F')
    (hF : FinX (reY Z P.Y)) : SPack (reD D Z) F' where
  X := reX Z P.X
  hb := (by with_unfolding_all exact (P.hb :))
  Y := reY Z P.Y
  fin := hF
  ψ := (by with_unfolding_all exact (P.ψ :))
  measTie := (by with_unfolding_all exact (measTie_reX Z P.measTie :))
  ψ_char := (by with_unfolding_all exact (P.ψ_char :))
  ψ_std := (by with_unfolding_all exact (P.ψ_std :))
  measCompat := (by with_unfolding_all exact (measCompat_reX Z P.measCompat :))
  locCompat := (by with_unfolding_all exact (fun w : D.what₂.Word => locCompat_reX Z (P.locCompat w) :))
  tr := (by with_unfolding_all exact (fun u : D.what₂.Word => reTr Z (P.tr u) (h u).2.1 (h u).2.2 :))
  into := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictInto_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.into u) :))
  bij := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictBij_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.bij u) :))
  lev := (by with_unfolding_all exact (fun u : D.what₂.Word => levelMatch_reTr Z (P.tr u) (h u).1 (h u).2.1 (h u).2.2 P.Y (P.lev u) :))
  isom := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictIsom_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y P.fin hF (P.isom u) :))
  inst := (by with_unfolding_all exact (P.inst :))
  G := reG Z P.G
  pin := (by with_unfolding_all exact (P.pin :))

section API

variable {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y))

theorem SPack.re_ψ : HEq (P.re Z h hF).ψ P.ψ := (by with_unfolding_all exact (HEq.refl P.ψ :))

end API

theorem conjHH_eEECre {X : HidaSetting D} (G : GoodOp X) (x : EEC X G) :
    conjHH (reX Z X) (reG Z G) (eEECre Z G x) = eHHre Z X (conjHH X G x) := (by with_unfolding_all exact (Eq.refl (eHHre Z X (conjHH X G x)) :))

example {X : HidaSetting D} (G : GoodOp X) :
    Module.finrank ℂ (EEC X G) = Module.finrank ℂ (EEC (reX Z X) (reG Z G)) := (eEECre Z G).toLinearEquiv.finrank_eq

example {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y)) :
    (P.re Z h hF).X.B.I = Formalism.L2.SG.InstExistsPf.instOf D := (by with_unfolding_all exact (P.inst :))

theorem exists_sameF_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) (F : ∀ u, Forms0 D u) :
    ∃ F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u, SameForms0LevelsAndValues (New.ofDiv D N ht) F F' := by
  let G : ∀ u : D.what₂.Word, Forms0 (GlobalTheory.EX.OB.setDiv D N ht) u := fun u =>
    { F u with
      atT := { (F u).atT with }
      cls0 := { (F u).cls0 with }
      val0 := { (F u).val0 with }
      lv0 := { (F u).lv0 with } }
  refine ⟨(by with_unfolding_all exact (G :)), fun u => ⟨?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.lev :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.y :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).val0.eY :))

theorem SPack.exists_re_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) {F : ∀ u, Forms0 D u}
    (P : SPack D F) :
    ∃ (F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u) (P' : SPack (reD D (New.ofDiv D N ht)) F'),
      P'.X = reX (New.ofDiv D N ht) P.X :=
  (exists_sameF_ofDiv N ht F).elim fun F' h => ⟨F', P.re _ h (finX_reY D _ P.X P.Y P.fin), rfl⟩

end GlobalTheory.Mem.SRe

end
end
