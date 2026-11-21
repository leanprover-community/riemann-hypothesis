import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes

open Module Submodule

noncomputable section

namespace Formalism.HN

namespace PolygonExample

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def e₀ : E2 := EuclideanSpace.single 0 1
def e₁ : E2 := EuclideanSpace.single 1 1
def Lx : Submodule ℤ E2 := Submodule.span ℤ {e₀, (2 : ℝ) • e₁}
def Px : Submodule ℤ E2 := Submodule.span ℤ {e₀}


theorem coord0 (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 0 = m := by
  simp [e₀, e₁]

theorem coord1 (m n : ℤ) : (m • e₀ + n • ((2 : ℝ) • e₁)) 1 = 2 * n := by
  simp [e₀, e₁]
  ring

theorem one_le_norm {x : E2} (hx : x ∈ Lx) (h0 : x ≠ 0) : 1 ≤ ‖x‖ := by
  have key : ∀ (y : E2) (i : Fin 2), |y i| ≤ ‖y‖ := by
    intro y i
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [Lx, Submodule.mem_span_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  by_cases hm : m = 0
  · have hn : n ≠ 0 := by
      rintro rfl
      subst hm
      exact h0 (by simp)
    have k1 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 1
    rw [coord1, abs_mul] at k1
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    norm_num at k1
    linarith
  · have k0 := key (m • e₀ + n • ((2 : ℝ) • e₁)) 0
    rw [coord0] at k0
    have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    linarith

theorem discrete_of_le (N : Submodule ℤ E2) (hN : N ≤ Lx) : DiscreteTopology N := by
  refine discreteTopology_of_isOpen_singleton_zero
    (Metric.isOpen_singleton_iff.2 ⟨1, one_pos, fun y hy => ?_⟩)
  by_contra hne
  have hy0 : (y : E2) ≠ 0 := fun h => hne (Subtype.ext h)
  have := one_le_norm (hN y.2) hy0
  rw [dist_zero_right, Submodule.coe_norm] at hy
  linarith

def vx : Fin 2 → E2 := ![e₀, (2 : ℝ) • e₁]

theorem vx_li : LinearIndependent ℤ vx := by
  unfold vx
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h0 := congrArg (fun v : E2 => v 0) hst
  have h1 := congrArg (fun v : E2 => v 1) hst
  simp only [coord0, coord1] at h0 h1
  simp only [PiLp.zero_apply] at h0 h1
  constructor
  · exact_mod_cast h0
  · have : (t : ℝ) = 0 := by linarith
    exact_mod_cast this

theorem Lx_eq : Lx = Submodule.span ℤ (Set.range vx) := by
  rw [Lx]
  congr 1
  ext x
  simp [vx, Fin.exists_fin_two, eq_comm]
  tauto

theorem rk_Lx : Formalism.F.rk Lx = 2 := by
  rw [Formalism.F.rk, Lx_eq, finrank_span_eq_card vx_li]
  simp

theorem covol_Lx : Formalism.F.covol Lx = 2 := by
  haveI := discrete_of_le Lx le_rfl
  let b : Basis (Fin 2) ℤ Lx := (Basis.span vx_li).map (LinearEquiv.ofEq _ _ Lx_eq.symm)
  have hb : ∀ i, (b i : E2) = vx i := fun i => by simp [b, Basis.span_apply]
  rw [Formalism.F.covolEqGram E2 Lx (Fin 2) b]
  have hg : Matrix.gram ℝ (fun i => (b i : E2)) = !![1, 0; 0, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.gram_apply, hb, vx, e₀, e₁, inner_smul_left, inner_smul_right,
        EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.norm_single] <;> norm_num
  rw [hg, Matrix.det_fin_two_of, show (1 : ℝ) * 4 - 0 * 0 = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]


theorem e₀_ne : e₀ ≠ 0 := by
  intro h
  have := congrArg (fun v : E2 => v 0) h
  simp [e₀] at this



end PolygonExample

section Main

open PolygonExample

local notation "ρx" => AddMonoidHom.id E2



theorem ex_bounds (N : Submodule ℤ E2) (hN : N ≤ Lx) :
    Formalism.F.rk N ≤ 2 ∧ Formalism.F.deg N ≤ 0 ∧ (Formalism.F.rk N = 2 → Formalism.F.deg N ≤ - Real.log 2) := by
  haveI hd : DiscreteTopology N := discrete_of_le N hN
  haveI : DiscreteTopology Lx := discrete_of_le Lx le_rfl
  haveI : Module.Finite ℤ Lx := by
    rw [Lx]
    exact Module.Finite.span_of_finite ℤ (Set.toFinite _)
  have hrk : Formalism.F.rk N ≤ 2 := by
    exact (Submodule.finrank_mono hN).trans rk_Lx.le
  have h2 : Formalism.F.rk N = 2 → 2 ≤ Formalism.F.covol N := by
    intro h
    have := Formalism.F.covolAntiSameRank E2 N Lx inferInstance hN (by rw [h, rk_Lx])
    rwa [covol_Lx] at this
  have h1 : 1 ≤ Formalism.F.covol N := by
    by_cases hb : N = ⊥
    · subst hb
      rw [(Formalism.F.covolBasic E2).1]
    obtain ⟨v, hv, hv0, hvn⟩ := Formalism.F.shortVector E2 N hd hb
    have hv1 := one_le_norm (hN hv) hv0
    obtain h | h | h : Formalism.F.rk N = 0 ∨ Formalism.F.rk N = 1 ∨ Formalism.F.rk N = 2 := by omega
    · rw [h] at hvn
      simp at hvn
      exact absurd hvn hv0
    · rw [h] at hvn
      simp at hvn
      linarith
    · linarith [h2 h]
  refine ⟨hrk, ?_, fun h => ?_⟩
  · simp only [Formalism.F.deg]
    linarith [Real.log_nonneg h1]
  · simp only [Formalism.F.deg]
    linarith [Real.log_le_log (by norm_num) (h2 h)]





end Main

end Formalism.HN
