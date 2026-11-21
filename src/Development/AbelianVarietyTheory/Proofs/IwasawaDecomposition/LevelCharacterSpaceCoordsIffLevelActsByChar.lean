import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AvgLevel
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem lvlE_range_iff : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  intro K _ _ _ S G _ _ r P ψ f
  have h := congrArg (fun s : Set S.Forms => f ∈ s) (GlobalTheory.Mem.LiftForms.range_lvlForm S r P ψ)
  simp only [Set.mem_range, GlobalTheory.Mem.LiftForms.lvlForm_apply] at h
  rw [h]
  rfl

end GlobalTheory.TopSpan
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  atlas_forward_decl GlobalTheory.TopSpan.lvlE_range_iff
