import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions




def HasDat {D : D7} (P : ModuliIntegralCharts.Prov D) (j : ℕ) : Prop :=
  ∃ dat : P.Dat, (j < D.R.m → P.rk dat = D.R.r) ∧ (j < D.R.m → P.jj dat = (D.R.sigW j).1)

def CuspZero {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) : Prop := ∀ w, Subsingleton (B.Cusp j w)

def toyPjOfCuspZero {D : D7} (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (hB : CuspZero B j) (dat : P.Dat)
    (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1) : WeightAlgebra.PJ D B P j where
  Forms := B.KO
  inc := fun _ => 0
  inc_inj := fun w a b _ => (hB w).elim a b
  inc_indep := by
    have : (fun w : WeightFamilies.Wt D j => LinearMap.range (0 : B.Cusp j w →ₗ[B.KO] B.KO)) = fun _ => ⊥ := by
      funext w; exact LinearMap.range_zero
    rw [this]
    intro w
    exact disjoint_bot_left
  inc_mul := fun _ _ _ _ => ⟨0, by simp⟩
  dat := dat
  dat_rk := h1
  dat_jj := h2
  Pt := fun _ => Empty
  pt66 := fun _ y => y.elim
  vAt := fun _ y => y.elim
  vAt_zero := fun _ y => y.elim
  vAt_ne_bot := fun _ y => y.elim
  vAt_add := fun _ y => y.elim
  vAt_smul := fun _ y => y.elim
  vAt_mul := fun _ y => y.elim
  Mlat_eq := fun w F => ⟨fun _ _ y => y.elim, fun _ => by
    have : F = 0 := (hB w).elim _ _
    rw [this]; exact Submodule.zero_mem _⟩
  thAll := fun _ => ⊥
  shortTh := fun _ => ⊥





def provBad (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) : WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun _ w => ((if w.n = 2 then ⊤ else ⊥ : Submodule K K) : Type)
  Mlat := fun _ _ => ⊥
  supN := fun _ _ σ F => ‖σ (F : K)‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  supN_smul := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ (F : K)‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  l2Norm_smul_alt := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0


def HasFullLocalData (D : D7) : Prop :=
  ∃ P : ModuliIntegralCharts.Prov D, ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j

theorem HasDat_of_full {D : D7} (P : ModuliIntegralCharts.Prov D)
    (hP : ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j) (j : ℕ) (h1 : 1 ≤ j) : HasDat P j := by
  have hk : 1 ≤ D.R.k := by
    have h2 := D.R.f_le_k
    have h3 : 0 < D.R.ord := D.R.ord_pos
    have h4 : D.R.f = 2 * D.R.ord := rfl
    omega
  by_cases hj : j < D.R.m
  · obtain ⟨w, hw1, hw2⟩ := hP D.R.r (D.R.sigW j).1
      (by simp only [Ranks.sigW]; omega) (by simp only [Ranks.sigW, Ranks.r]; omega)
    exact ⟨w, fun _ => hw1, fun _ => hw2⟩
  · obtain ⟨w, _, _⟩ := hP 2 1 le_rfl le_rfl
    exact ⟨w, fun h => absurd h hj, fun h => absurd h hj⟩



end Formalism.MainNotions.DIV.Inh

end
