import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Mathlib

namespace Formalism.FourierDecayAlt.P.LagrangeExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7


theorem extractK : ExtractK := by
  intro V _ _ K
  induction K with
  | zero =>
    intro d s W grid _ _ y₀
    simp
    congr 1
    exact Subsingleton.elim _ _
  | succ K ih =>
    intro d s W grid hP hg y₀
    set c := y₀ (Fin.last K) with hc
    have hP' : PolyStep K d (fun a => s a.castSucc)
        (fun m (y' : Fin K → ℝ) => W m (Fin.snoc (α := fun _ => ℝ) y' c)) := by
      intro a y'
      obtain ⟨cc, h1, h2⟩ := hP a.castSucc (Fin.snoc (α := fun _ => ℝ) y' c)
      refine ⟨cc, by simpa using h1, fun t => ?_⟩
      have := h2 t
      rw [← Fin.snoc_update] at this
      simpa using this
    have ih' := ih d _ _ (fun a => grid a.castSucc) hP' (fun a => hg _) (Fin.init y₀)
    simp only [hc, Fin.snoc_init_self] at ih'
    have hl : ∀ y' : Fin K → ℝ, s (Fin.last K) • W K (Fin.snoc (α := fun _ => ℝ) y' c) =
        ∑ i, ((lagCo (grid (Fin.last K)) i : ℝ) : ℂ) •
          W (K + 1) (Fin.snoc (α := fun _ => ℝ) y' (grid (Fin.last K) i)) := by
      intro y'
      obtain ⟨cc, h1, h2⟩ := hP (Fin.last K) (Fin.snoc (α := fun _ => ℝ) y' c)
      rw [Fin.val_last] at h1 h2
      rw [← h1, ChebyshevExtremalPolynomials.lead_complex (grid (Fin.last K)) (hg _) cc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h2, Fin.update_snoc_last]
    rw [Fin.prod_univ_castSucc, mul_comm, mul_smul, ih', Finset.smul_sum]
    rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [smul_comm, ← hc, hl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun a => grid a (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1)) (i, j') a)) =
        Fin.snoc (α := fun _ => ℝ) (fun a : Fin K => grid a.castSucc (j' a)) (grid (Fin.last K) i) := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [Fin.snocEquiv]
    rw [e, smul_smul, Fin.prod_univ_castSucc]
    congr 1
    simp [Fin.snocEquiv]


lemma norm_le_sum {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {K d : ℕ} (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ) (hP : PolyStep K d s W)
    (hg : ∀ a, Function.Injective (grid a)) (y₀ : Fin K → ℝ) :
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      ∑ j : Fin K → Fin (d + 1), (∏ a, |lagCo (grid a) (j a)|) * ‖W K fun a => grid a (j a)‖ := by
  have h := extractK V K d s W grid hP hg y₀
  calc (∏ a, ‖s a‖) * ‖W 0 y₀‖ = ‖(∏ a, s a) • W 0 y₀‖ := by rw [norm_smul, norm_prod]
    _ = ‖∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ := by
        rw [h]
    _ ≤ ∑ j : Fin K → Fin (d + 1), ‖((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ :=
        norm_sum_le _ _
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]


lemma lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    lagCo y j ≠ 0 := by
  unfold lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.mem_erase.mp hi).1 (hy h).symm




end Formalism.FourierDecayAlt.P.LagrangeExtraction

namespace Formalism.FourierDecayAlt.P


theorem extract_K_bound : Formalism.FourierDecayAlt.F7.ExtractK := LagrangeExtraction.extractK




end Formalism.FourierDecayAlt.P
