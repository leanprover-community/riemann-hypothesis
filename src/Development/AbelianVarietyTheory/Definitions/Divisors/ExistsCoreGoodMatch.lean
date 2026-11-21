import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCorePb
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


section Cover

variable {T : Core D} {j : ℕ} {Y : Deep T j} {e e' : ℕ} {o o' : ℝ}

theorem chi_eq_one (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) (la) (γ)
    (hγ : γ ∈ ((Y.U σ).X k).Γ) : ((Y.U σ).X k).χ la γ = 1 :=
  GlobalTheory.OneEmbeddingProbe.chi_eq_one _ (h.chiTriv σ hσ) k la γ hγ

theorem exp_unique (h : Y.Good e o) (h' : Y.Good e' o') : e = e' :=
  Nat.pow_right_injective (by norm_num : 2 ≤ 15) (h.pd.symm.trans h'.pd)

theorem size_nonneg (h : Y.Good e o) : 0 ≤ o := (Real.log_natCast_nonneg _).trans h.deg

theorem rank_eq (h : Y.Good e o) : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (h.unf Y.d.c₂.F.val.toRingHom rfl).1

theorem pull_add {f f' : T.R j} {g g' : Rul Y.d.Xo₂ Y.d.c₂} (h : Y.Pull f g) (h' : Y.Pull f' g') : Y.Pull (f + f') (g + g') := by
  intro k _ _ _ _ _ a b y₂ y' y c1 c2 c3 c4
  exact (evalAt_add _ _ g g' y₂).trans ((congrArg₂ (· + ·) (h k a b y₂ y' y c1 c2 c3 c4) (h' k a b y₂ y' y c1 c2 c3 c4)).trans
    (evalAt_add _ _ f f' y).symm)

theorem pull_mul {f f' : T.R j} {g g' : Rul Y.d.Xo₂ Y.d.c₂} (h : Y.Pull f g) (h' : Y.Pull f' g') : Y.Pull (f * f') (g * g') := by
  intro k _ _ _ _ _ a b y₂ y' y c1 c2 c3 c4
  exact (evalAt_mul _ _ g g' y₂).trans ((congrArg₂ (· * ·) (h k a b y₂ y' y c1 c2 c3 c4) (h' k a b y₂ y' y c1 c2 c3 c4)).trans
    (evalAt_mul _ _ f f' y).symm)



end Cover

section Base

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)




end Base

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ)

theorem exZ_shiftG (s : ℤ) : exZ Dw (shiftG Dw a (2 * m) s) = exOf Dw (laOf Dw a (2 * m) + s • hodgeWt Dw) m := by
  have h1 := exOf_add (laOf Dw a (2 * m)) (s • hodgeWt Dw) (m : ℤ) 0
  have h2 := exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) m
  have h3 : laOf Dw a (2 * m) = weightOf Dw (fun x => (a x : ℤ)) m := by simp [laOf]
  rw [add_zero] at h1
  rw [h1, h3, h2]
  funext x
  rw [shiftG, exZ_add]
  simp only [wtZ, exOf, Pi.add_apply]
  push_cast
  rfl




end Weights


end GlobalTheory.CovTop.Model

end
