import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkLatTupUpdate
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LowestInvariantLeDelta
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def nC (v : X.Pl) (i l : ℕ) : ℕ :=
  (p ^ X.G.P.n' v) ^ ((i - l) * (X.t + 1 - l)) * Formalism.G0.gaussBinom (p ^ X.G.P.n' v) (X.t + 1) l

theorem latAt_succ_upd (v : X.Pl) (j : ℕ) (L' : (X.Pj (j + 1)).Tup)
    (L1 : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v)) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v))) :
    X.latAt v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj (j + 1)).W u) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq u))
    (X.vJ (j + 1) v) L1 L'

theorem latAt_zero_upd (v : X.Pl) (L' : (X.Pj 0).Tup)
    (L1 : Submodule ((X.Pj 0).W (X.vJ 0 v)) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq (X.vJ 0 v))) :
    X.latAt v 0 (Function.update L' (X.vJ 0 v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj 0).W u) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq u))
    (X.vJ 0 v) L1 L'

theorem countG (hC : CountLoc) (v : X.Pl) (j i : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup)
    (hL : (X.Pj j).IsLatTup L) (hL' : (X.Pj (j + 1)).IsLatTup L') :
    ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.ind v j L (Function.update L' (X.vJ (j + 1) v) L1) =
      ∑ l ∈ range (i + 1), nC X v i l •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) (L (X.vJ j v)), X.ind v j (Function.update L (X.vJ j v) A1) L' := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  cases j with
  | zero =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + 1) (X.G.P.m + (0 + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj (0 + 1)) (X.vJ (0 + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj (0)) (X.vJ (0) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_zero_upd]
      rfl
  | succ j =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1) (X.G.P.m + ((j + 1) + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj ((j + 1) + 1)) (X.vJ ((j + 1) + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj ((j + 1))) (X.vJ ((j + 1)) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem upd_back (L : P.Tup) (w : Fin P.nV) (A1 : Submodule (P.W w) (Fin (P.m + 1) → P.Qq w)) :
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A1) w (L w) = L := by
  exact (Function.update_idem (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) A1 (L w) L).trans
    (Function.update_eq_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w L)

theorem upd_at (L : P.Tup) (w : Fin P.nV) (A1 : Submodule (P.W w) (Fin (P.m + 1) → P.Qq w)) :
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A1 w = A1 := by
  first
    | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A1 L
    | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A1 L

end Gen

theorem prod_zpow_upd {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (x : K) (hx : x ≠ 0) (f g : ι → ℤ) (v : ι)
    (d : ℤ) (h1 : g v = f v + d) (h2 : ∀ u, u ≠ v → g u = f u) :
    ∏ u, x ^ (g u) = (∏ u, x ^ (f u)) * x ^ d := by
  rw [← Finset.mul_prod_erase Finset.univ (fun u => x ^ g u) (Finset.mem_univ v),
    ← Finset.mul_prod_erase Finset.univ (fun u => x ^ f u) (Finset.mem_univ v)]
  have hprod : ∏ u ∈ Finset.univ.erase v, x ^ g u = ∏ u ∈ Finset.univ.erase v, x ^ f u :=
    Finset.prod_congr rfl (fun u hu => by rw [h2 u (Finset.ne_of_mem_erase hu)])
  rw [hprod, h1, zpow_add₀ hx]
  ring

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

def hv (X : Sys p) (v : X.Pl) : ℤ := ((X.G.P.n' v / 2 : ℕ) : ℤ)

def Traw (j : ℕ) (s1 s2 : X.G.Kf) (Ξ : MvPowerSeries (X.ZA j) Y.Kc) (G : (X.Pj j).Xsp) : XspC (X.Pj (j + 1)) Y.Kc :=
  s1 • Y.DelF j G (s2 • Ξ)

theorem Traw_mul (j : ℕ) (s1 s2 c1 c2 : X.G.Kf) (Ξ : MvPowerSeries (X.ZA j) Y.Kc) (G : (X.Pj j).Xsp) :
    Traw Y j (s1 * c1) (s2 * c2) Ξ G = (c1 * c2) • Traw Y j s1 s2 Ξ G := by
  unfold Traw
  rw [mul_comm s2 c2, mul_smul c2 s2, map_smul, smul_smul, smul_smul]
  congr 1
  ring

def T0 (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    XspC (X.Pj (j + 1)) Y.Kc :=
  Traw Y j (Y.eS j La * (Y.eT j La')⁻¹)
    (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 La'.2)))
    (Y.Xi v j (Y.aw v j La La') f) G

theorem integral_span_coordinates (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) {ι : Type} (s : Finset ι)
    (f : ι → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La La' (∑ x ∈ s, f x) G = ∑ x ∈ s, T0 Y a a' v j La La' (f x) G := by
  unfold T0 Traw
  rw [map_sum, Finset.smul_sum, map_sum, Finset.smul_sum]

theorem kernel_nsmul (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (n : ℕ)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La La' (n • f) G = (n : X.G.Kf) • T0 Y a a' v j La La' f G := by
  unfold T0 Traw
  rw [map_nsmul, smul_comm _ n, map_nsmul, smul_comm _ n, Nat.cast_smul_eq_nsmul]

def cA (X : Sys p) (a' : X.G.Kf) (v : X.Pl) (j i : ℕ) : X.G.Kf :=
  (p : X.G.Kf) ^ (X.vm v (j + 1) * i) * (a' ^ (-(i : ℤ)) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t j : ℤ) * i))

def cC (X : Sys p) (a : X.G.Kf) (v : X.Pl) (j k : ℕ) : X.G.Kf :=
  (p : X.G.Kf) ^ (X.vm v (j + 1) * k) * (a ^ (k : ℤ) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k))

theorem kernel_target_identity (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ) (La : X.Lt j)
    (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup) (i : ℕ)
    (L1 : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v)) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v)))
    (hE : IsEdge p ((X.Pj (j + 1)).n' (X.vJ (j + 1) v)) i ⟨L1, L' (X.vJ (j + 1) v)⟩)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La (c', Function.update L' (X.vJ (j + 1) v) L1) f G =
      cA X a' v j i • T0 Y a a' v j La (c', L') f G := by
  have e1 : Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = Y.len v (j + 1) L' - i := by
    have := Y.len_edge (j + 1) (X.vJ (j + 1) v) i L' L1 hE
    rwa [vB_vJ] at this
  have e2 : ∀ u, u ≠ v → Y.len u (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = Y.len u (j + 1) L' := by
    intro u hu
    exact Y.len_other (j + 1) (X.vJ (j + 1) v) u L' L1 (by rw [vB_vJ]; exact hu)
  have e3 : Y.eT j (c', Function.update L' (X.vJ (j + 1) v) L1) =
      Y.eT j (c', L') * (p : X.G.Kf) ^ (-(X.vm v (j + 1) * i)) := by
    unfold Pend.eT
    apply prod_zpow_upd _ hp _ _ v
    · show X.vm v (j + 1) * Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = _
      rw [e1]; ring
    · intro u hu
      show X.vm u (j + 1) * Y.len u (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = _
      rw [e2 u hu]
  have e4 : Y.volE v j La.2 (Function.update L' (X.vJ (j + 1) v) L1) =
      Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i := by
    unfold Pend.volE
    rw [e1]; ring
  have e5 := Y.aw_tgt v j La (c', L') L1
  unfold T0
  show Traw Y j (Y.eS j La * (Y.eT j (c', Function.update L' (X.vJ (j + 1) v) L1))⁻¹)
    (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1)) *
      (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 (Function.update L' (X.vJ (j + 1) v) L1))))
    (Y.Xi v j (Y.aw v j La (c', Function.update L' (X.vJ (j + 1) v) L1)) f) G = _
  rw [e5, e3, e1, e4]
  have s1 : Y.eS j La * (Y.eT j (c', L') * (p : X.G.Kf) ^ (-(X.vm v (j + 1) * i)))⁻¹ =
      (Y.eS j La * (Y.eT j (c', L'))⁻¹) * (p : X.G.Kf) ^ (X.vm v (j + 1) * i) := by
    rw [mul_inv, ← zpow_neg, neg_neg, mul_assoc]
  have s2 : a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) L' - i) *
      (p : X.G.Kf) ^ (-(hv X v * (Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i))) =
      (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) L') * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 L'))) *
        (a' ^ (-(i : ℤ)) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t j : ℤ) * i)) := by
    rw [sub_eq_add_neg, zpow_add₀ ha',
      show -(hv X v * (Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i)) =
        -(hv X v * Y.volE v j La.2 L') + hv X v * (NN X.G.P.m X.t j : ℤ) * i by ring, zpow_add₀ hp]
    ring
  rw [s1, s2, Traw_mul]
  rfl

theorem kernel_source_identity (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha : a ≠ 0) (v : X.Pl) (j : ℕ) (La : X.Lt j)
    (La' : X.Lt (j + 1)) (k : ℕ)
    (A1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
    (hE : IsEdge p ((X.Pj j).n' (X.vJ j v)) k ⟨La.2 (X.vJ j v), A1⟩)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j (La.1, Function.update La.2 (X.vJ j v) A1) La' f G =
      cC X a v j k • T0 Y a a' v j La La' f G := by
  have e1 : Y.len v j (Function.update La.2 (X.vJ j v) A1) = Y.len v j La.2 + k := by
    have := Y.len_edge j (X.vJ j v) k (Function.update La.2 (X.vJ j v) A1) (La.2 (X.vJ j v))
      (by rw [upd_at]; exact hE)
    rw [vB_vJ, upd_back] at this
    linarith
  have e2 : ∀ u, u ≠ v → Y.len u j (Function.update La.2 (X.vJ j v) A1) = Y.len u j La.2 := by
    intro u hu
    exact Y.len_other j (X.vJ j v) u La.2 A1 (by rw [vB_vJ]; exact hu)
  have e3 : Y.eS j (La.1, Function.update La.2 (X.vJ j v) A1) =
      Y.eS j La * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) := by
    unfold Pend.eS
    apply prod_zpow_upd _ hp _ _ v
    · show X.vm v (j + 1) * Y.len v j (Function.update La.2 (X.vJ j v) A1) = _
      rw [e1]; ring
    · intro u hu
      show X.vm u (j + 1) * Y.len u j (Function.update La.2 (X.vJ j v) A1) = _
      rw [e2 u hu]
  have e4 : Y.volE v j (Function.update La.2 (X.vJ j v) A1) La'.2 =
      Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k := by
    unfold Pend.volE
    rw [e1]; ring
  have e5 := Y.weight_update_at_place v j La La' A1
  unfold T0
  show Traw Y j (Y.eS j (La.1, Function.update La.2 (X.vJ j v) A1) * (Y.eT j La')⁻¹)
    (a ^ (Y.len v j (Function.update La.2 (X.vJ j v) A1)) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(hv X v * Y.volE v j (Function.update La.2 (X.vJ j v) A1) La'.2)))
    (Y.Xi v j (Y.aw v j (La.1, Function.update La.2 (X.vJ j v) A1) La') f) G = _
  rw [e5, e3, e1, e4]
  have s1 : Y.eS j La * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) * (Y.eT j La')⁻¹ =
      (Y.eS j La * (Y.eT j La')⁻¹) * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) := by ring
  have s2 : a ^ (Y.len v j La.2 + k) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(hv X v * (Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k))) =
      (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 La'.2))) *
        (a ^ (k : ℤ) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k)) := by
    rw [zpow_add₀ ha,
      show -(hv X v * (Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k)) =
        -(hv X v * Y.volE v j La.2 La'.2) + hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k by ring, zpow_add₀ hp]
    ring
  rw [s1, s2, Traw_mul]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

def ThEq (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) : Prop :=
  ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Y.ThF j La La' = (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * Y.volE v j La.2 La'.2))) •
      Y.Xi v j (Y.aw v j La La') (X.ind v j La.2 La'.2)

variable {Y}

theorem kernel_eq_theta {a a' : X.G.Kf} {v : X.Pl} {j : ℕ} (hTh : ThEq Y a a' v j) (La : X.Lt j) (La' : X.Lt (j + 1))
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup La'.2) (G : (X.Pj j).Xsp) :
    Y.ker j La La' G = T0 Y a a' v j La La' (X.ind v j La.2 La'.2) G := by
  unfold Pend.ker Pend.kerF T0 Traw
  rw [hTh La La' h1 h2]
  rfl

theorem ker_sum (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) {ι : Type} (s : Finset ι) (G : ι → (X.Pj j).Xsp) :
    Y.ker j La La' (∑ x ∈ s, G x) = ∑ x ∈ s, Y.ker j La La' (G x) := by
  unfold Pend.ker Pend.kerF
  rw [map_sum, LinearMap.sum_apply, Finset.smul_sum]

theorem cC_ne (hp : (p : X.G.Kf) ≠ 0) {a : X.G.Kf} (ha : a ≠ 0) (v : X.Pl) (j k : ℕ) : cC X a v j k ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hp) (mul_ne_zero (zpow_ne_zero _ ha) (zpow_ne_zero _ hp))

theorem ker_dn_sum (hC : CountLoc) (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} (ha : a ≠ 0) (ha' : a' ≠ 0) {v : X.Pl}
    {j : ℕ} (hTh : ThEq Y a a' v j) (La : X.Lt j) (hLa : (X.Pj j).IsLatTup La.2) (c' : X.Lv.comp (j + 1))
    (L' : (X.Pj (j + 1)).Tup) (hL' : (X.Pj (j + 1)).IsLatTup L') (i : ℕ) (G : (X.Pj j).Xsp) :
    ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        Y.ker j La (c', Function.update L' (X.vJ (j + 1) v) L1) G =
      cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) (La.2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ • Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) (c', L') G := by
  have e1 : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      Y.ker j La (c', Function.update L' (X.vJ (j + 1) v) L1) G =
        cA X a' v j i • T0 Y a a' v j La (c', L') (X.ind v j La.2 (Function.update L' (X.vJ (j + 1) v) L1)) G := by
    intro L1 hL1
    have hE := (mem_EE _).1 hL1
    rw [kernel_eq_theta hTh La _ hLa (hk_latTup_update _ hL' _ L1 hE.1)]
    exact kernel_target_identity Y hp a a' ha' v j La c' L' i L1 hE _ G
  rw [Finset.sum_congr rfl e1, ← Finset.smul_sum, ← integral_span_coordinates, countG X hC v j i La.2 L' hLa hL', integral_span_coordinates]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [kernel_nsmul, integral_span_coordinates]
  congr 1
  refine Finset.sum_congr rfl fun A1 hA1 => ?_
  have hE := (mem_UP _).1 hA1
  rw [kernel_eq_theta hTh (La.1, Function.update La.2 (X.vJ j v) A1) (c', L') (hk_latTup_update _ hLa _ A1 hE.2.1) hL']
  have := kernel_source_identity Y hp a a' ha v j La (c', L') (i - l) A1 hE
    (X.ind v j (Function.update La.2 (X.vJ j v) A1) L') G
  rw [this, smul_smul, inv_mul_cancel₀ (cC_ne hp ha v j (i - l)), one_smul]

theorem hk_adj (D : Formalism.BasicNotions.D7) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) (v : X.Pl) (j : ℕ) (hj : j < X.mm) (k : ℕ)
    (F : X.Fm j) (hF : F ∈ X.FQ j) (La' : X.Lt (j + 1)) (hLa' : (X.Pj (j + 1)).IsLatTup La'.2) :
    ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2) =
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ • Y.ker j La La' (X.Tm v k j F La.1 La.2) := by
  classical
  apply MvPolynomial.ext
  intro n
  let φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc := fun c L L1 =>
    if (X.Pj j).IsLatTup L1 then MvPolynomial.coeff n (Y.ker j (c, L1) La' (F c L)) else 0
  have hφ : ∀ c (γ : (X.Lv.lev j c).Γ) L L1,
      φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1 := by
    intro c γ L L1
    simp only [φ]
    by_cases h : (X.Pj j).IsLatTup L1
    · rw [if_pos h, if_pos ((latTup_smul _ _ γ L1).2 h), (Eqv_of_FQ X hF).2 c γ L,
        h5b j hj c L1 La' γ (F c L) (vt_FQ X hF c L) h hLa']
    · rw [if_neg h, if_neg (fun h' => h ((latTup_smul _ _ γ L1).1 h'))]
  have key := h6 j hj.le (X.vJ j v) k φ hφ
  have hs : ∀ (La : X.Lt j) (z : Y.Kc), ((X.stab j La : X.G.Kf))⁻¹ • z = ((X.stab j La : Y.Kc))⁻¹ * z := by
    intro La z
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun La hLa => ?_
    have hlat := Y.Rep_lat j La hLa
    rw [MvPolynomial.coeff_smul, hs, MvPolynomial.coeff_sum]
    congr 1
    refine Eq.trans ?_ (finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))).symm
    refine Finset.sum_congr rfl fun A1 hA1 => ?_
    have hE := (mem_UP _).1 hA1
    simp only [φ]
    rw [if_pos (hk_latTup_update _ hlat _ A1 hE.2.1)]
  · refine Finset.sum_congr rfl fun La hLa => ?_
    have hlat := Y.Rep_lat j La hLa
    rw [MvPolynomial.coeff_smul, hs]
    congr 1
    refine Eq.trans (finsum_mem_eq_finite_toFinset_sum _ (edges_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))) ?_
    have e : X.Tm v k j F La.1 La.2 = ∑ L0 ∈ EE (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        F La.1 (Function.update La.2 (X.vJ j v) L0) := Tminus_eq (X.Pj j) (X.vJ j v) k (F La.1) La.2
    rw [e, ker_sum, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun L0 _ => ?_
    simp only [φ]
    rw [if_pos hlat]

def KAdj (Y : Pend X) (j : ℕ) (Cl Yb : Type) [Fintype Cl] [Fintype Yb] (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j) : Prop :=
  ∀ (v : X.Pl) (k : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k ((La x y).2 (X.vJ j v)),
        Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) La' (F (La x y).1 (La x y).2) =
      ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, Y.ker j (La x y) La' (X.Tm v k j F (La x y).1 (La x y).2)

theorem up_finsum (j : ℕ) (v : X.Pl) (k : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G : (X.Pj j).Xsp) :
    ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
        (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) k ⟨La.2 (X.vJ j v), L1⟩),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) L1) La' G =
      ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' G :=
  finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))

theorem kadj_entry (D : Formalism.BasicNotions.D7) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) (j : ℕ) (hj : j < X.mm) :
    KAdj Y j {La // La ∈ Y.Rep j} Unit (fun x => X.stab j x.1) (fun x _ => x.1) := by
  intro v k F hF La' hLa'
  have h := hk_adj D h5b h6 v j hj k F hF La' hLa'
  have hs : ∀ (n : ℕ) (z : XspC (X.Pj (j + 1)) Y.Kc), ((n : X.G.Kf))⁻¹ • z = ((n : Y.Kc))⁻¹ • z := by
    intro n z
    rw [← algebraMap_smul Y.Kc ((n : X.G.Kf))⁻¹ z, map_inv₀, map_natCast]
  simp only [hs] at h
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact ((Finset.sum_coe_sort (Y.Rep j) (fun La => ((X.stab j La : Y.Kc))⁻¹ •
      ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2))).trans h).trans
    (Finset.sum_coe_sort (Y.Rep j) (fun La => ((X.stab j La : Y.Kc))⁻¹ •
      Y.ker j La La' (X.Tm v k j F La.1 La.2))).symm

theorem ksa_of_adm (D : Formalism.BasicNotions.D7) (h4 : ArchimedeanSignatureMatching D X Y) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) {j : ℕ} (hj : j < X.mm) :
    ∃ (cK : Y.Kc) (Cl Yb : Type) (_ : Fintype Cl) (_ : Fintype Yb) (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j),
      KSum Y j cK Cl Yb wt La ∧ KAdj Y j Cl Yb wt La := by
  rcases Nat.lt_or_ge (j + 1) X.mm with h | h
  · obtain ⟨cK, _, _, h4'⟩ := h4.1 j h
    exact ⟨cK, _, _, inferInstance, inferInstance, _, _, ksum_entry Y hj.le h4', kadj_entry D h5b h6 j hj⟩
  · obtain ⟨cK, _, _, Cl, Yb, iC, iY, wt, La, h1, h2, h3, h5⟩ := h4.2 j (by omega)
    refine ⟨cK, Cl, Yb, iC, iY, wt, La, ⟨h1, h2, h3⟩, fun v k F hF La' hLa' => ?_⟩
    have := h5 v k F hF La' hLa'
    simp only [up_finsum] at this
    exact this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem hk_scal {K : Type} [Field K] (P a a' e : K) (hP : P ≠ 0) (ha : a ≠ 0) (h vm N g i l : ℤ) :
    P ^ (-(h * i * ((N + g) - i))) * (P ^ (vm * i) * (a' ^ (-i) * P ^ (h * N * i))) *
        (P ^ (2 * h * ((i - l) * (g - l))) * (P ^ (h * (l * (g - l))) * e)) *
        (P ^ (vm * (i - l)) * (a ^ (i - l) * P ^ (h * (N + g) * (i - l))))⁻¹ =
      ((a * a')⁻¹) ^ i * ((a * P ^ vm) ^ l * e) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
  have e1 : P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹ =
      P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
    rw [← zpow_neg, ← zpow_neg]
    simp only [← zpow_add₀ hP]
    congr 1
    ring
  have e2 : (a ^ (i - l))⁻¹ = (a ^ i)⁻¹ * a ^ l := by
    rw [zpow_sub₀ ha, inv_div, div_eq_mul_inv, mul_comm]
  calc _ = (P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹) *
        (a ^ (i - l))⁻¹ * a' ^ (-i) * e := by ring
    _ = (P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l))))) * ((a ^ i)⁻¹ * a ^ l) * a' ^ (-i) * e := by
      rw [e1, e2]
    _ = _ := by
      rw [inv_zpow, mul_zpow, mul_zpow, ← zpow_mul, mul_inv, zpow_neg a' i]
      ring

theorem hk_esymm_smul {K σ : Type} [Field K] [Fintype σ] (c : K) (f : σ → K) (l : ℕ) :
    MvPolynomial.eval (fun x => c * f x) (MvPolynomial.esymm σ K l) =
      c ^ l * MvPolynomial.eval f (MvPolynomial.esymm σ K l) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

theorem hk_esymm_zero {K σ : Type} [Field K] [Fintype σ] (l : ℕ) (h : Fintype.card σ < l) :
    MvPolynomial.esymm σ K l = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.2 (by rwa [Finset.card_univ]), Finset.sum_empty]

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def eBe (v : X.Pl) (l : ℕ) : X.G.Kf :=
  MvPolynomial.eval (fun x : Fin (X.t + 1) => X.qh v x.val) (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)

theorem nC_cast (hp : (p : X.G.Kf) ≠ 0) (v : X.Pl) (i l : ℕ) :
    (nC X v i l : X.G.Kf) = (p : X.G.Kf) ^ (2 * hv X v * (((i - l : ℕ) : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) *
      ((p : X.G.Kf) ^ (hv X v * ((l : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) * eBe X v l) := by
  obtain ⟨k, hk⟩ := (X.std v).even
  have h1 : X.G.P.n' v / 2 = k := by omega
  have h2 : p ^ X.G.P.n' v = (p ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hQ : (((p ^ k : ℕ) : ℕ) : X.G.Kf) ≠ 0 := by push_cast; exact pow_ne_zero _ hp
  have hG := Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric X.G.Kf (p ^ k) (X.t + 1) l hQ
  have hf : Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1) = fun x => X.qh v x.val := funext fun x => by
    have := beFam_eq X v x
    rwa [h1] at this
  have hb : Formalism.InvariantFactorPaths.G7.eF (Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1)) l = eBe X v l := by
    unfold Formalism.InvariantFactorPaths.G7.eF eBe
    rw [hf]
  unfold nC
  rw [h2]
  push_cast at hG ⊢
  rw [hG, hb]
  unfold hv
  rw [h1]
  congr 1
  · rw [← pow_mul, ← pow_mul, ← zpow_natCast]
    congr 1
    push_cast
    ring
  · congr 1
    rw [← pow_mul, ← zpow_natCast]
    congr 1

theorem NN_succ (k1 t j : ℕ) : (NN k1 t (j + 1) : ℤ) = (NN k1 t j : ℤ) + ((t + 1 : ℕ) : ℤ) := by
  unfold NN
  push_cast
  ring

theorem hk_coef (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha : a ≠ 0) (v : X.Pl) (j i l : ℕ) (hl : l ≤ i) :
    (p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i))) * cA X a' v j i * (nC X v i l : X.G.Kf) *
        (cC X a v j (i - l))⁻¹ =
      ((a * a')⁻¹) ^ i * (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
        (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ)))) := by
  rw [hk_esymm_smul, nC_cast X hp]
  show _ = ((a * a')⁻¹) ^ i * ((a * (p : X.G.Kf) ^ (X.vm v (j + 1))) ^ l * eBe X v l) * _
  by_cases hg : l ≤ X.t + 1
  · have := hk_scal (p : X.G.Kf) a a' (eBe X v l) hp ha (hv X v) (X.vm v (j + 1)) (NN X.G.P.m X.t j : ℤ)
      ((X.t + 1 : ℕ) : ℤ) i l
    unfold cA cC
    rw [NN_succ, Nat.cast_sub hl, Nat.cast_sub hg, ← zpow_natCast ((a * a')⁻¹) i,
      ← zpow_natCast (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) l]
    exact this
  · have h0 : eBe X v l = 0 := by
      unfold eBe
      rw [hk_esymm_zero l (by simpa using not_le.1 hg), map_zero]
    rw [h0]
    simp

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem hk_point (Y : Pend X) (hC : CountLoc) (hT : RestTmFQ X)
    (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} {cK : Y.Kc} (ha : a ≠ 0) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ)
    (hTh : ThEq Y a a' v j) {Cl Yb : Type} [Fintype Cl] [Fintype Yb] {wt : Cl → ℕ} {La : Cl → Yb → X.Lt j}
    (hS : KSum Y j cK Cl Yb wt La) (hAd : KAdj Y j Cl Yb wt La)
    (i : ℕ) (F : X.Fm j) (hF : F ∈ X.FQ j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup)
    (hL' : (X.Pj (j + 1)).IsLatTup L') :
    X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ l ∈ range (i + 1), (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) •
        X.Kz j (X.Tm v (i - l) j F) c' L' := by
  obtain ⟨hlat, _, h4⟩ := hS
  apply MvPolynomial.map_injective (algebraMap X.G.Kf Y.Kc) (algebraMap X.G.Kf Y.Kc).injective
  have eT : X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1) :=
    Tminus_eq (X.Pj (j + 1)) (X.vJ (j + 1) v) i (X.Kz j F c') L'
  rw [eT, map_sum, map_sum]
  have eL : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1)) =
        ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
          Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) := by
    intro L1 hL1
    exact h4 F hF c' _ (hk_latTup_update _ hL' _ L1 ((mem_EE _).1 hL1).1)
  rw [Finset.sum_congr rfl eL, Finset.sum_comm]
  have eL2 : ∀ x ∈ (Finset.univ : Finset Cl), ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
        Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) =
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, (cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ •
            Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro x _
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ker_dn_sum hC hp ha ha' hTh (La x y) (hlat x y) c' L' hL' i _
  rw [Finset.sum_congr rfl eL2]
  have eR : ∀ l ∈ range (i + 1), MvPolynomial.map (algebraMap X.G.Kf Y.Kc)
      ((cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • X.Kz j (X.Tm v (i - l) j F) c' L') =
      (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • (cK • ∑ x : Cl,
        ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro l _
    rw [map_smulK Y, h4 _ (hT v (i - l) j F hF) c' L' hL', hAd v (i - l) F hF (c', L') hL',
      Finset.smul_sum (r := cK)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl eR]
  have hs : ∀ (r : X.G.Kf) (z : XspC (X.Pj (j + 1)) Y.Kc), r • z = algebraMap X.G.Kf Y.Kc r • z :=
    fun r z => (algebraMap_smul Y.Kc r z).symm
  simp only [hs, Finset.smul_sum, smul_smul]
  symm
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun A1 _ => ?_
  congr 1
  simp only [map_mul, map_inv₀, map_natCast]
  ring

theorem heckeCondition_of_adm (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hC : CountLoc) (hT : RestTmFQ X) :
    RestHecke X := by
  obtain ⟨_, _, _, _, _, h3b, h4, h5, h5b, h6, _, _, _⟩ := hA
  intro v
  have hfr := frac_of_place X v
  have he := eO_pos X v
  have hp : (p : X.G.Kf) ≠ 0 := pKf_ne Y
  have h5' : ∀ j, ∃ a a' : X.G.Kf, j < X.mm → (X.vEqK a 0 ∧ X.vEqK a' 0 ∧ ThEq Y a a' v j) := by
    intro j
    by_cases hj : j < X.mm
    · obtain ⟨u, u', h1, h2, h3⟩ := h5 v j hj
      exact ⟨u, u', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, 1, fun h => absurd h hj⟩
  choose a a' H using h5'
  refine ⟨fun l => (a (l - 1) * a' (l - 1))⁻¹, fun l => a (l - 1) * (p : X.G.Kf) ^ (X.vm v l), ?_, ?_, ?_⟩
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2, _⟩ := H (l - 1) (by omega)
    have := vEqK_inv X hfr (vEqK_mul X hfr h1 h2)
    simpa using this
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, _, _⟩ := H (l - 1) (by omega)
    have := vEqK_mul X hfr h1 (vEqK_ppow X hfr he (X.vm v l))
    simpa using this
  · intro j hj i F hF
    obtain ⟨h1, h2, hTh⟩ := H j hj
    obtain ⟨cK, Cl, Yb, iC, iY, wt, La, hS, hAd⟩ := ksa_of_adm D h4 h5b h6 hj
    have ha := vEqK.ne_zero X h1
    have ha' := vEqK.ne_zero X h2
    show X.ecal v i (j + 1) (X.Kz j F) = ((a j * a' j)⁻¹ ^ i) • X.Kz j (∑ l ∈ range (i + 1),
      (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
        (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)
    funext c' L'
    by_cases hL' : (X.Pj (j + 1)).IsLatTup L'
    · have eR : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) =
          ∑ l ∈ range (i + 1),
            ((MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
              (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
              (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ))))) •
              X.Kz j (X.Tm v (i - l) j F) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold Sys.ecal
        rw [map_smul, map_smul, smul_smul]
        rfl
      rw [eR]
      show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
        X.Tm v i (j + 1) (X.Kz j F) c' L' = _
      rw [hk_point Y hC hT hp ha ha' v j hTh hS hAd i F hF c' L' hL']
      simp only [Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      congr 1
      have := hk_coef X hp (a j) (a' j) ha v j i l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
      rw [mul_assoc ((a j * a' j)⁻¹ ^ i)] at this
      rw [← this]
      ring
    · have e1 : X.Tm v i (j + 1) (X.Kz j F) c' L' = 0 :=
        (restTmEquiv X (j + 1) v i _ (Eqv_of_FQ X (h3b j hj F hF))).1 c' L' hL'
      have e2 : X.ecal v i (j + 1) (X.Kz j F) c' L' = 0 := by
        show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
          X.Tm v i (j + 1) (X.Kz j F) c' L' = 0
        rw [e1, smul_zero]
      rw [e2]
      have hmem : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) ∈ X.FQ (j + 1) :=
        h3b j hj _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
          (Submodule.smul_mem _ _ (hT v (i - l) j F hF)))
      rw [Pi.smul_apply, Pi.smul_apply, FQ_zero_off X hmem c' L' hL', smul_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
