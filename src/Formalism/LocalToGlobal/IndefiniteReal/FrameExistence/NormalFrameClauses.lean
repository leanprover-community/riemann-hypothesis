import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Links Formalism.IndefR.Lev

variable {D : D7}



end Formalism.IndefR.Seed.Frm

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def NormalClausesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (NormalFrames (betaYOf βY) e ev z κ s Pg Pg ∧ NormalFrame0 (betaYOf βY 0) Pg Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf βY 0) (βW i) eW ι Pg

variable (D) in

def FramesExistG (Pg : Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalClausesG Pg βY βW


open Classical in

theorem framesExistG_of_framesExist {T : Type} (t0 : T) {Pg : Finset (Pl D.host.E)}
    (h : FramesExist D Pg ∅ (fun _ : T => ∅)) : FramesExistG D Pg := by
  obtain ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, e, ev, z, κ, s, hN, hW⟩ := h
  have h0 := hN t0
  simp only [Finset.union_empty] at h0
  exact ⟨ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW, hSD, e, ev, z, κ, s, h0, hW⟩

end Formalism.IndefR.Seed.Frm

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.IndefR.Mi IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed.Frm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def XBasesG (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) : Prop :=
  ∀ j : ℕ, j < D.R.m → ∃ βX : GL (Fin (D.sp.X j).rank) (EAf D), Formalism.L2.DIV.IsFrame βX (l0X (D.sp.X j)) ∧
    ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
      ∀ (col : Fin (D.sp.Y j).rank) (l : Fin (D.sp.X j).rank), IsXCol (D := D) j col l →
        ∀ r : Fin (D.sp.Y j).rank, toEAf D ei * (betaYOf βY j).val r col =
          toEAf D ei * (xMat (D := D) j).mulVec (fun i => βX.val i l) r

def NormalFrameConditionsDiagonal (Pg : Finset (Pl D.host.E)) (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D))
    (βW : ∀ i : Fin D.R.m, GL (Fin (Wc D i).rank) (EAf D)) : Prop :=
  NormalClausesG Pg βY βW ∧ XBasesG Pg βY

variable (D) in

def FramesExistDiagonal (Pg : Finset (Pl D.host.E)) : Prop :=
  ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
    (ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E))
    (ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E))
    (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
    (βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)) (βX : GL (Fin D.sp.X'.rank) (EAf D))
    (βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)),
    SDFrames ΛY ΛX ΛV ΛW βY βX βV βW ∧ NormalFrameConditionsDiagonal Pg βY βW

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem framesOKg2_iff (Rl : RealDat3 D A3 Ks) :
    FramesOKg2 Rl ↔ NormalFrameConditionsDiagonal Rl.toRealDat.Pg Rl.toRealDat.βY Rl.toRealDat.βW := by
  first
  | exact Iff.rfl
  | (unfold FramesOKg2 NormalFrameConditionsDiagonal; done)

end Formalism.IndefR.Seed.Frm

end
end
