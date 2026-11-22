module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealRecPins
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Formalism.SharpRestriction.GlobalTheoremInputs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {Bd : BdT}

def Ev {𝒜 : FamClass} (σ : RawSel Bd 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (q : BdP Bd) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, q _ _ _ (σ Fm hc x hx i)

def EvW (q : BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : W3 𝒜 Fm, Ev σ Fm (w3_a hc) q

def EvWC (prem : ∀ {eps : ℝ}, FamP eps → Prop) (q : ℝ → ℝ → BdP Bd) (𝒜 : FamClass) (σ : RawSel Bd 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm CH => ∀ hc : W3 𝒜 Fm, prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ev σ Fm (w3_a hc) (q C CH)

theorem ev_of_atAll {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {q : BdP Bd} (h : AtAll q 𝒜 σ) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) :
    Ev σ Fm hc q := ⟨0, fun x hx _ i => h Fm hc x hx i⟩

end GlobalTheory.Fc.Ind

end
