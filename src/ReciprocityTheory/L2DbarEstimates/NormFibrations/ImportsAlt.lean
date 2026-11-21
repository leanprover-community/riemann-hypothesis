import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO
import ReciprocityTheory.L2DbarEstimates.SymmetricSections.NormVanishOfHoloSection

section
universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormFibStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (U : Set (V n)),
    IsCoveringMapOn z U → (∀ x, z x ∈ U) → (∀ y : V n, (z ⁻¹' {y}).Finite) → ConnectedSpace M →
    ∃ δ : ℕ, ∀ y : V n, (z ⁻¹' {y}).encard ≤ δ

theorem normFib : NormFibStatement.{u} := by
  intro n M _ z U hcov himg hfin hconn

  have hloc : ∀ x : M, ∀ᶠ x' in 𝓝 x, (z ⁻¹' {z x'}).encard = (z ⁻¹' {z x}).encard := by
    intro x
    obtain ⟨hd, W, hxW, hW, hzW, H, hH⟩ := hcov (z x) (himg x)
    have hev : ∀ w ∈ W, IsEvenlyCovered z w (z ⁻¹' {z x}) :=
      fun w hw => ⟨hd, W, hw, hW, hzW, H, hH⟩
    filter_upwards [hzW.mem_nhds (show x ∈ z ⁻¹' W from hxW)] with x' hx'
    exact Set.encard_congr (hev (z x') hx').fiberHomeomorph.toEquiv.symm
  obtain ⟨x0⟩ := (inferInstance : Nonempty M)
  have hS : IsClopen {x : M | (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard} := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
      rw [hx']
      exact hx
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      filter_upwards [hloc x] with x' hx'
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hx', hx]
  have hall := hS.eq_univ ⟨x0, rfl⟩
  refine ⟨(z ⁻¹' {z x0}).ncard, fun y => ?_⟩
  rw [(hfin (z x0)).cast_ncard_eq]
  by_cases hy : ∃ x, z x = y
  · obtain ⟨x, rfl⟩ := hy
    have hx : (z ⁻¹' {z x}).encard = (z ⁻¹' {z x0}).encard := Set.eq_univ_iff_forall.1 hall x
    exact hx.le
  · have h0 : z ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hy ⟨x, h⟩
    rw [h0, Set.encard_empty]
    exact zero_le

end ReciprocityTheory.L2DbarEstimates
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

def NormOrdStatement : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] (z : M → V n) (f : M → ℂ) (x : M) (m : ℕ),
    IsLocalHomeomorph z → Holo n z f → VanishesBeyond n z f x m →
    Norm.VanishOrder n z f x (m + 1)

theorem normOrd : NormOrdStatement.{u} := by
  intro n M _ z f x m hz hf hv
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  obtain ⟨C, hC⟩ := Y.bound_of_iteratedFDeriv_eq_zero (f ∘ e.symm) e.target (z x)
    e.open_target hzx (hf e he) m (hv e he hx)
  have h1 : ∀ᶠ y in 𝓝 x, ‖(f ∘ e.symm) (z y)‖ ≤ C * ‖z y - z x‖ ^ (m + 1) :=
    hz.continuous.continuousAt.tendsto.eventually hC
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ e.source := e.open_source.mem_nhds hx
  rw [Norm.VanishOrder, Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [h1, h2] with y hy hys
  have hy' : e.symm (z y) = y := by rw [he hys]; exact e.left_inv hys
  simp only [Function.comp_apply, hy'] at hy
  rw [norm_pow, norm_norm]
  exact hy

end ReciprocityTheory.L2DbarEstimates
end

section
universe u

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

theorem norm (n : ℕ) (M : Type u) [TopologicalSpace M] : NORMStatement n M := by
  intro z Δ u C m hΔ hcov himg hfin hconn hu hgr hvan
  have hpre : z ⁻¹' {y : V n | MvPolynomial.eval (fun i => y i) Δ ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall himg
  have hz : IsLocalHomeomorph z := by
    have h := hcov.isLocalHomeomorphOn
    rw [hpre] at h
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 h
  obtain ⟨δ, hδ⟩ := normFib.{u} n M z _ hcov himg hfin hconn
  have hΔ0 : Norm.polyAt n Δ 0 ≠ 0 := by
    have h0 : Norm.polyAt n Δ 0 = MvPolynomial.constantCoeff Δ := by
      rw [← MvPolynomial.eval_zero]
      rfl
    rw [h0]
    exact hΔ
  funext x
  exact Norm.normVanish.{u} n M z Δ δ m C u hΔ0 hcov himg hδ hu hgr
    (fun x hx => normOrd.{u} n M z u x m hz hu (hvan x hx)) x

end ReciprocityTheory.L2DbarEstimates
end
