import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Fr

variable (D : D7)

def PlaceOK1 (Ch Cg b dist dinf : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b 1 ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    (∀ s, |L.lam s - lamSH D.R (D.hc v) s| ≤ dinf) ∧ IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec

def BpLoc1 (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ^ A) * jNorm2 L f μsec

variable {D}


theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : GapAtLeast ε lam h) (hh : h' ≤ h) :
    GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)




end Fr


def BesselExpansionLocalFrame : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 CA Cinf Cgf Cg₀ : ℝ), 2 ≤ Cg₀ ∧ (∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) ∧
    ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        BpLoc1 D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C2 5



end Formalism.L2.SG.Pf.BesselExpansion
