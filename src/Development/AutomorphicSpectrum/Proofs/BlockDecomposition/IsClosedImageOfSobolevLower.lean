import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachAdm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound

section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob Filter
open GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CompanionTheory.SobComplete

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Dw_sub_of_sm {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hxy : Sm ε σ (x - y) := sm_iff.2 (Submodule.sub_mem _ (sm_iff.1 hx) (sm_iff.1 hy))
  have h := Dw_add hσ hl hxy hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem tendsto_sobNorm_zero {σ : Mx n → (H →L[ℂ] H)} {u : ℕ → H} (S : List (List (Mx n)))
    (h : ∀ l ∈ S, Tendsto (fun k => ‖l.foldr (dRep σ) (u k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => sobNorm σ S (u k)) atTop (𝓝 0) := by
  induction S with
  | nil => simpa [sobNorm] using tendsto_const_nhds
  | cons l S ih =>
    have h1 := h l List.mem_cons_self
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    simp [sobNorm]

theorem smoothVec_complete_of_unitary (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UJset ε) σ) (w : ℕ → H) (hw : ∀ k, SmoothVec (lieSet ε) σ (w k))
    (hC : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0,
      ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) :
    ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Tendsto (fun k => sobNorm σ S (w k - w₀)) atTop (𝓝 0) := by
  have hρ : ModRep ε σ := GlobalTheory.FamSmooth.modRep_of_isURepOn hσ
  have hmem : ∀ l : List (lie (Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := fun l X hX => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  let U : ℕ → List (lie (Jm ε)) → H := fun k l => Dw σ (l.map Subtype.val) (w k)
  have hU : ∀ k, U k ∈ Fam ε σ := fun k => GlobalTheory.SobUnif.smooth_fam hσ (hw k)
  have hcau : ∀ l, CauchySeq fun k => U k l := fun l => by
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨K, hK⟩ := hC [l.map Subtype.val] (by simpa using hmem l) δ hδ
    refine ⟨K, fun k hk m hm => ?_⟩
    rw [dist_eq_norm]
    show ‖Dw σ (l.map Subtype.val) (w k) - Dw σ (l.map Subtype.val) (w m)‖ < δ
    rw [← Dw_sub_of_sm hσ (hmem l) (hw k) (hw m)]
    exact (norm_Dw_le_sobNorm σ List.mem_cons_self _).trans_lt (hK k hk m hm)
  choose v hv using fun l => cauchySeq_tendsto_of_complete (hcau l)
  have hvF : v ∈ Fam ε σ :=
    (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).mem_of_tendsto (tendsto_pi_nhds.2 hv) (Eventually.of_forall hU)
  obtain ⟨hs, hd⟩ := GlobalTheory.SobUnif.fam_smooth hσ hvF
  refine ⟨v [], hs, fun S hS => tendsto_sobNorm_zero S fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ := GlobalTheory.SobUnif.exists_lift l (hS l hl)
  have h1 : Tendsto (fun k => U k l' - v l') atTop (𝓝 0) := by
    simpa using (hv l').sub_const (v l')
  have h2 := h1.norm
  rw [norm_zero] at h2
  refine h2.congr fun k => ?_
  show ‖Dw σ (l'.map Subtype.val) (w k) - v l'‖ = ‖Dw σ (l'.map Subtype.val) (w k - v [])‖
  rw [Dw_sub_of_sm hσ (hmem l') (hw k) hs, hd l']

theorem smoothVec_complete : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ w : ℕ → H, (∀ k, SmoothVec (lieSet ε) σ (w k)) → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) → ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Filter.Tendsto (fun k => sobNorm σ S (w k - w₀)) Filter.atTop (nhds 0) :=
  fun n ε H _ _ _ σ hσ _ w hw hC => smoothVec_complete_of_unitary n ε H σ hσ w hw hC

end GlobalTheory.CompanionTheory.SobComplete

end
end

section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob

namespace GlobalTheory.CompanionTheory.SmoothClosed

theorem smoothVec_sub {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {u v : H}
    (hu : SmoothVec Lie σ u) (hv : SmoothVec Lie σ v) : SmoothVec Lie σ (u - v) := by
  intro k Xs hX
  simpa only [map_sub] using (hu k Xs hX).sub (hv k Xs hX)

theorem tendsto_seminorm_sub {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {q : Seminorm ℂ E} (hq : Continuous q) {u : ℕ → E} {y : E} (hu : Filter.Tendsto u Filter.atTop (nhds y)) :
    Filter.Tendsto (fun k => q (u k - y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k => u k - y) Filter.atTop (nhds (y - y)) := hu.sub_const y
  rw [sub_self] at h
  simpa [Function.comp_def, map_zero] using (hq.tendsto 0).comp h

theorem isClosed_image_of_sobolev_lower : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w)) → IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hmod T hT hlow
  haveI : FirstCountableTopology E := hmod.withSeminorms.firstCountableTopology
  refine IsSeqClosed.isClosed ?_
  intro x y hx hxy
  choose w hw hTw using hx
  have hcauchy : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ := by
    intro S hS δ hδ
    obtain ⟨q, hq, hqb⟩ := hlow S hS
    have ht := tendsto_seminorm_sub hq hxy
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨K, fun k hk m hm => ?_⟩
    calc sobNorm σ S (w k - w m) ≤ q (T (w k - w m)) := hqb _ (smoothVec_sub (hw k) (hw m))
      _ = q ((x k - y) - (x m - y)) := by rw [T.map_sub, hTw, hTw, sub_sub_sub_cancel_right]
      _ ≤ q (x k - y) + q (x m - y) := map_sub_le_add q _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hK k hk) (hK m hm)
      _ = δ := add_halves δ
  obtain ⟨w0, hw0, hconv⟩ := GlobalTheory.CompanionTheory.SobComplete.smoothVec_complete n ε H σ hU hI w hw hcauchy
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨-, hT2⟩ := hT
  have hT' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds (T w0)) := by
    refine (hmod.withSeminorms.tendsto_nhds _ _).2 ?_
    intro i δ hδ
    obtain ⟨S, C, hS, hb⟩ := hT2 i
    have hC : Filter.Tendsto (fun k => C * sobNorm σ S (w k - w0)) Filter.atTop (nhds 0) := by
      simpa using (hconv S hS).const_mul C
    filter_upwards [hC.eventually (gt_mem_nhds hδ)] with k hk
    calc p i (T (w k) - T w0) = p i (T (w k - w0)) := by rw [T.map_sub]
      _ ≤ C * sobNorm σ S (w k - w0) := hb _ (smoothVec_sub (hw k) hw0)
      _ < δ := hk
  have hx' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds y) := by
    simp only [hTw]
    exact hxy
  exact tendsto_nhds_unique hT' hx'

end GlobalTheory.CompanionTheory.SmoothClosed

end
end
