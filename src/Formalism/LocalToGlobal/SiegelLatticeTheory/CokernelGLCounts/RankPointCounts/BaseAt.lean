import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerFix

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def sgnU : GLp p :=
  ⟨Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p,
    Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p⟩

def tau : GG p →* GG p where
  toFun x := (x.1, MulOpposite.op (sgnU p * x.2.unop * sgnU p))
  map_one' := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      show sgnU p * (1 : GLp p) * sgnU p = 1
      rw [mul_one, hs]
  map_mul' x y := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      simp only [Prod.snd_mul, MulOpposite.unop_mul, MulOpposite.unop_op]
      calc sgnU p * (y.2.unop * x.2.unop) * sgnU p
          = sgnU p * y.2.unop * (sgnU p * sgnU p) * x.2.unop * sgnU p := by rw [hs]; group
        _ = _ := by group

theorem tau_tau (x : GG p) : tau p (tau p x) = x := by
  have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
  ext1
  · rfl
  · apply MulOpposite.unop_injective
    show sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = x.2.unop
    calc sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = (sgnU p * sgnU p) * x.2.unop * (sgnU p * sgnU p) := by
          group
      _ = _ := by rw [hs]; group

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

theorem sconj_apply (ρ : MP p) (a b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      (-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
  simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem sconj_up {ρ : MP p} (h : IsUpUni ρ) :
    IsUpUni (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [sconj_apply, (h a b).1 hab]; simp
  · subst hab
    rw [sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]; simp

theorem tau_second_value (x : GG p) : (((tau p x).2.unop : GLp p) : MP p) =
    Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p := rfl

theorem tau_mem_UP {x : GG p} (hx : x ∈ UP p) : tau p x ∈ UP p :=
  ⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩

theorem tau_mem_KP {x : GG p} (hx : x ∈ KP M p) : tau p x ∈ KP M p := by
  refine ⟨hx.1, ?_⟩
  show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)
  rw [tau_second_value]
  obtain ⟨h1, h2, h3⟩ := hx.2
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [sconj_apply, h2 a b hab]; simp
  · rw [sconj_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b))
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (Z : MP p) : MP p :=
  Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w

theorem phi_smul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {x : GG p}
    (hx : x ∈ UP p) (Z : MP p) : phi p δ T T' w (x • Z) = tau p x • phi p δ T T' w Z := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  have hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w := by
    have hu := sconj_up p hx.2
    refine Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl)
      (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]
    rw [if_neg h]
  simp only [phi, smul_def, tau_second_value]
  show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w =
    ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p)
  rw [Matrix.mul_add, Matrix.add_mul, hc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]

theorem phi_inj (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {Z Z' : MP p}
    (h : phi p δ T T' w Z = phi p δ T T' w Z') : Z = Z' := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  unfold phi at h
  have h2 := add_right_cancel h
  calc Z = Z * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    _ = Z' * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [h2]
    _ = Z' := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def BaseAt (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ c : UP p, phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = (c : GG p) • a.mat ∧
    ∀ x : UP p, ((x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) ↔ (x : GG p) • a.mat = a.mat)

end Formalism.L2.SG.Pf.CountAt
end
end
