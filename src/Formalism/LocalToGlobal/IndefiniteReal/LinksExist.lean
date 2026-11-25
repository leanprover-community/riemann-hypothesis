module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

variable {D : D7}

section Stages2L

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

theorem preliminary_of_vacuum_update (h : R.Pre1 F) (ωY ωX vac vacX vY vX ItY ItX ioY ioX Th) : (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem preliminary_of_frame_update (h : R.Pre1 F) (ωP vacP vP ioP thF thG) : (R.upd4 ωP vacP vP ioP thF thG).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem full_Y_of_theta_update (h : R.FullY) (ωP vacP vP ioP thF thG) : (R.upd4 ωP vacP vP ioP thF thG).FullY := h

theorem preliminary_of_index_update (h : R.Pre1 F) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem full_Y_of_index_update (h : R.FullY) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).FullY := h

theorem full_P_of_index_update (h : R.FullP) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).FullP := h

theorem preliminary_of_scalar_update (h : R.Pre1 F) (kap lam) : (R.upd6 kap lam).Pre1 F :=
  ⟨⟨h.1.lev, h.1.red_R, h.1.red_L, h.1.levels, h.1.record, ⟨h.1.fam.tie, h.1.fam.Sb, h.1.fam.roots, h.1.fam.pl_onto, h.1.fam.degR, h.1.fam.degL, h.1.fam.muVal, h.1.fam.etaVal⟩, h.1.inf, h.1.vpos, h.1.cX, h.1.cV, h.1.prX, h.1.order, h.1.std⟩,
    ⟨h.2.inf, h.2.vpos, h.2.cX, h.2.cV, h.2.prX, h.2.HX, h.2.HV, h.2.HE, h.2.HW, h.2.gE, h.2.gW, h.2.jX, h.2.jV, h.2.νY, h.2.νY', h.2.ν0, h.2.νX, h.2.νV, h.2.νW, h.2.BV, h.2.order⟩⟩

theorem full_Y_of_scalar_update (h : R.FullY) (kap lam) : (R.upd6 kap lam).FullY := h

theorem full_P_of_scalar_update (h : R.FullP) (kap lam) : (R.upd6 kap lam).FullP := h

end RealDat

end Stages2L

section Stages3

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face D A}

theorem exists_cond {X : Sort*} (x₀ : X) {c : Prop} {p : X → Prop} (h : c → ∃ x, p x) : ∃ x, c → p x := by
  by_cases hc : c
  · obtain ⟨x, hx⟩ := h hc; exact ⟨x, fun _ => hx⟩
  · exact ⟨x₀, fun h' => absurd h' hc⟩

theorem kerY_args (hW : WeilExistsFull D) (hV : VacExistsO D) (hS : StepVecExists D) (hPt : PtStable D) (hC : CartanOK D)
    (hD : SelfDualOK D) (hT : Formalism.IndefR.Fin.VecThetaSD D) (hF : SeedFacts D A Ks F) (R : RealDat D A Ks) (h : R.Pre1 F) :
    ∃ ωY ωX vac vacX vY vX, (R.upd3 ωY ωX vac vacX vY vX R.ItY R.ItX R.ioY R.ioX R.Th).KerY := by
  obtain ⟨hsp, hid⟩ := hF R h.1
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have sd : ∀ j, j < D.R.m → IsSelfDualC (Yc D j) (R.ΛY j) ∧ IsFrame (R.βY j) (R.ΛY j) := fun j hj => by
    obtain ⟨c, hc⟩ := h.1.lev.βY j hj
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  have sdX : IsSelfDualC D.sp.X' R.ΛX ∧ IsFrame R.βX R.ΛX := by
    obtain ⟨c, hc⟩ := h.1.lev.βX
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  choose ωY hωY using fun t k => exists_cond (1 : GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ))
    fun hk : k + 1 < D.R.m => hW R.ψ _ _ _ _ h.1.std ((hsp t).1 k hk).1 ((hsp t).1 k hk).2.1 ((hsp t).1 k hk).2.2.1 ((hsp t).1 k hk).2.2.2
  choose ωX hωX using fun t => hW R.ψ (Yc D (D.R.m - 1)) D.sp.X' _ _ h.1.std (hsp t).2.1.1 (hsp t).2.1.2.1 (hsp t).2.1.2.2.1
    (hsp t).2.1.2.2.2
  choose vac hvac using fun k => exists_cond (0 : WO (Yc D k) (Yc D (k + 1)) → ℂ) fun hk : k + 1 < D.R.m =>
    hV R.ψ R.θ h.1.std h.1.inf (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (D.sp.Y_sig _) (D.sp.Y_sig _)
      (hC.1 _ _ _ (D.sp.Y_sig _)) (hC.1 _ _ _ (D.sp.Y_sig _)) (R.ΛY k) (R.ΛY (k + 1)) (sd k (by omega)).1 (sd (k + 1) hk).1
  obtain ⟨vacX, hvacX⟩ := hV R.ψ R.θ h.1.std h.1.inf (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (D.sp.Y_sig _) D.sp.X'_sig (hC.1 _ _ _ (D.sp.Y_sig _)) (hC.1 _ _ _ D.sp.X'_sig) (R.ΛY (D.R.m - 1)) R.ΛX (sd _ hm).1 sdX.1
  choose vY hvY using fun t k => exists_cond (0 : WO (Yc D k) (Yc D (k + 1)) → ℂ) fun hk : k + 1 < D.R.m =>
    hS R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1))
      (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (sd k (by omega)).1 (sd (k + 1) hk).1 (sd k (by omega)).2 (sd (k + 1) hk).2
      (hid t).1 (hid t).2 (vac k) (hvac k hk)
  choose vX hvX using fun t =>
    hS R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX
      (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) (sd _ hm).1 sdX.1 (sd _ hm).2 sdX.2 (hid t).1
      (hid t).2 vacX hvacX
  exact ⟨ωY, ωX, vac, vacX, vY, vX, ⟨hωY, hωX⟩, hvY, hvX,
    fun t k hk P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P (hT.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sd k (by omega)).1 (sd (k + 1) hk).1
      (sd k (by omega)).2 (sd (k + 1) hk).2 (hvY t k hk)),
    fun t P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P (hT.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sd _ hm).1 sdX.1 (sd _ hm).2 sdX.2
      (hvX t))⟩

theorem exists_localWeil_vacuum_kernel (hW : WeilExistsFull D) (hV : VacExistsO D) (hS : ThPVecExists D) (hPt : PtStable D) (hC : CartanOK D)
    (hD : SelfDualOK D) (hT : Formalism.IndefR.Fin.VecThetaSD D) (hF : SeedFacts D A Ks F) (R : RealDat D A Ks) (h : R.Pre1 F) :
    ∃ ωP vacP vP, (R.upd4 ωP vacP vP R.ioP R.thF R.thG).KerP := by
  obtain ⟨hsp, hid⟩ := hF R h.1
  have sdV : ∀ i, IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsFrame (R.βV i) (R.ΛV i) := fun i => by
    obtain ⟨c, hc⟩ := h.1.lev.βV i
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  have sdW : ∀ i, IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsFrame (R.βW i) (R.ΛW i) := fun i => by
    obtain ⟨c, hc⟩ := h.1.lev.βW i
    exact ⟨hD _ _ _ _ hc, hc.1⟩
  choose ωP hωP using fun (i : Fin D.R.m) t => hW R.ψ (Vc D i) (Wc D i) _ _ h.1.std ((hsp t).2.2 i).1 ((hsp t).2.2 i).2.1
    ((hsp t).2.2 i).2.2.1 ((hsp t).2.2 i).2.2.2
  choose vacP hvac using fun i : Fin D.R.m => hV R.ψ R.θ h.1.std h.1.inf (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A)))
    (D.sp.V_sig _) (D.sp.W_sig _) (hC.2 _ (D.sp.V_sig _) (h.1.vpos i)) (hC.1 _ _ _ (D.sp.W_sig _)) (R.ΛV i) (R.ΛW i) (sdV i).1 (sdW i).1
  choose vP hvP using fun (i : Fin D.R.m) t => hS R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) (sdV i).1 (sdW i).1 (sdV i).2 (sdW i).2 (hid t).1 (hid t).2 (vacP i) (hvac i)
  exact ⟨ωP, vacP, vP, hωP, hvP, fun i t P => hPt R.ψ R.θ h.1.std h.1.inf _ _ _ _ _ _ _ P
    (hT.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sdV i).1 (sdW i).1 (sdV i).2 (sdW i).2 (hvP i t))⟩

end Stages3

end Formalism.IndefR.Links

end
