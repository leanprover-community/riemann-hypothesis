import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondCommDistinctPlaces
import Formalism.LocalToGlobal.HermitianForms.TiedSym

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.GlobalTheoryTheory

variable (D : D7) (u : D.what₂.Word)

variable {D u} in

def ChiFin0 {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)

def FormsTwistCompatibilityFamily : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), ChiFin0 T

def FiSt0 : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Uop D u 0 v φ ∈ (D.fm u).Fi 0 ∧ Dop D u 0 v φ ∈ (D.fm u).Fi 0

def CrossDia0 : Prop :=
  ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi 0, ∀ a,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def UnfAll0 : Prop := ∀ v, Nonempty (Unf D u 0 v)

def FiSt0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → FiSt0 D u

def CrossDia0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → CrossDia0 D u

def UnfAll0T : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → UnfAll0 D u

def IntegralityLevelZeroUnderForms : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → LocalLatticeBases.HeckeIntegralLevelZero D u

variable {D u}


theorem integrality_of_rationality_local (h : IntAtT D u) : LocalLatticeBases.HeckeIntegralLevelZero D u :=
  fun w hw hs v => h 0 (Nat.zero_le _) w hw hs v

variable {eps : ℝ}

theorem hI_tied (Fm : FamP eps) (tie : FamU Fm fun D u => FormsTwistCompatibilityFamily D u ∧ admS D u)
    (hI : ∀ (D : D7) (u : D.what₂.Word), IntegralityLevelZeroUnderForms D u) : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero := by
  obtain ⟨x0, hx0⟩ := tie
  refine ⟨x0, fun x hx hx1 i u hs => ?_⟩
  obtain ⟨hT, hA⟩ := hx0 x hx hx1 i u hs
  exact hI _ _ hT hA hs


end Formalism.MainNotions.RT

end
