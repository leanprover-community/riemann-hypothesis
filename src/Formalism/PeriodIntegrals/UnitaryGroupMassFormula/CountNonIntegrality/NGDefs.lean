import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NotIntAllOfLoc

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrIntG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → ∀ a,
      (g.e (frFac δ p a)).1 ∈ 𝒪[(D.s.atP p).Fp]

def CongG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → ∀ a b,
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).1 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) * s) ∧
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).2 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) * s) ∧
          (∃ s : 𝒪[(D.s.atP p).Fp], (g.e ((D.s.atP p).ιE (Z a b))).1 + (g.e ((D.s.atP p).ιE (Z b a))).2 +
            (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
              (((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) + (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) else 0) =
              (g.q : (D.s.atP p).Fp) ^ 2 * s)

theorem frFac_last (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) :
    frFac δ p (Fin.last D.R.rS) = 1 := by
  unfold frFac
  simp only [Fin.val_last, Nat.sub_self, pow_zero, Ring.inverse_one]

theorem frFac_coord (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D)
    (g : Loc.SplitG (M p).L) (a : Fin (D.R.rS + 1)) :
    (g.e (frFac δ p a)).2 = (g.e (frFac δ p a)).1 := by
  have hc : (M p).L.cj (frFac δ p a) = frFac δ p a := by
    rw [(hA p).2.2.1, cj_frFac]
  have h := g.e_cj (frFac δ p a)
  rw [hc] at h
  have h2 := congrArg Prod.snd h
  rw [Prod.snd_swap] at h2
  exact h2

theorem zhatLoc_eq (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (p : PlF D) (Z : MatZ D)
    (a b : Fin (D.R.rS + 1)) :
    ZhatLoc M δ p Z a b = frFac δ p b * frFac δ p a * (D.s.atP p).ιE (Z a b) := by
  have h : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [ZhatLoc, Matrix.of_apply]
  rw [h, cj_frFac]


end PI.CntNotIntW
