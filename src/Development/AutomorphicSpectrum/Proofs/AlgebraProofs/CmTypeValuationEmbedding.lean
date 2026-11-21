import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsMonogenicSeparating
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder

section
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem block_monogenic_of_residual_character : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  exact @PositivityTheory.Xgn.exists_monogenic_separating

end GlobalTheory.CompanionTheory.Ar.Flat
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_unavailable_one : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig

theorem sum_embeddings_eq_trace (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* C, s x = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  classical
  let Ω := AlgebraicClosure C
  let f : (E →+* C) → (E →ₐ[ℚ] Ω) := fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)
  have hf : ∀ s y, f s y = algebraMap C Ω (s y) := fun s y => rfl
  have hinj : Function.Injective f := by
    intro s t hst
    ext y
    have h := congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst
    simp only [hf] at h
    exact (algebraMap C Ω).injective h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hc, AlgHom.card]⟩
  have key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x :=
    trace_eq_sum_embeddings Ω (x := x)
  rw [← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)] at key
  simp only [hf] at key
  apply (algebraMap C Ω).injective
  rw [map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]

theorem sum_eigProj (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M) :
    ∑ s, HT.eigProj ρ s y = y := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    calc (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      _ = algebraMap (𝓞 E) E (∑ j, b.repr 1 j • b j) := by rw [b.sum_repr]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    calc Algebra.trace ℚ E (HT.dualInt E k) = Algebra.traceForm ℚ E (HT.dualInt E k) 1 := by
          rw [Algebra.traceForm_apply, mul_one]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by
          conv_lhs => rw [h1]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ((b.repr 1 k : ℤ) : ℚ) := by
          simp only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C) := by
    intro k
    rw [sum_embeddings_eq_trace E C hc, htr, map_intCast]
  calc ∑ s, HT.eigProj ρ s y = ∑ s : E →+* C, ∑ k, s (HT.dualInt E k) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [HT.eigProj]
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hb]
    _ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsum]
    _ = ρ (∑ k, b.repr 1 k • b k) y := by
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    _ = y := by
        rw [b.sum_repr, map_one, Module.End.one_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_eigen_projections_eq_self : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [Fintype (E →+* C)], Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M), ∑ s, HT.eigProj ρ s y = y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig.sum_eigProj
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block

theorem sum_eq_sum_subtype {α β : Type} [Fintype α] [AddCommMonoid β] (D : α → Prop)
    [Fintype {s // D s}] (G : α → β) (h : ∀ s, ¬ D s → G s = 0) :
    ∑ s, G s = ∑ s : {s // D s}, G s.1 := by
  classical
  rw [← Finset.sum_filter_of_ne (p := D) (fun x _ hx => by_contra fun hD => hx (h x hD))]
  exact Finset.sum_subtype _ (fun x => by simp) G

section

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem mem_freeLattice {S : Type} {a : S → w.valuationSubring} {r : ℕ} {x : S → Fin r → C} :
    x ∈ freeLattice a r ↔ ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
      x s i = ((f.eval (a s) : w.valuationSubring) : C) := Iff.rfl

def valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)) :
    Submodule w.valuationSubring ((E →+* C) → w.valuationSubring) :=
  Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)

theorem mul_mem_valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    {f g : (E →+* C) → w.valuationSubring} (hf : f ∈ valSpan emb) (hg : g ∈ valSpan emb) :
    f * g ∈ valSpan emb := by
  unfold valSpan at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    induction hg using Submodule.span_induction with
    | mem y h =>
      obtain ⟨b, rfl⟩ := h
      exact Submodule.subset_span ⟨a * b, by funext s; simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable {M : Type} [AddCommGroup M] [Module C M] [Module w.valuationSubring M]
  [IsScalarTower w.valuationSubring C M] {ρ : 𝓞 E →+* Module.End C M}
  {X : Submodule w.valuationSubring M} {N : ℕ} {t : Fin N → M}

theorem rho_mem (h : HT.IsFreeOn ρ X t) (a : 𝓞 E) (j : Fin N) : ρ a (t j) ∈ X := by
  have e := congrArg (fun u => ρ u (t j)) ((RingOfIntegers.basis E).sum_repr a)
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply] at e
  rw [← e]
  refine sum_mem fun k _ => zsmul_mem ?_ _
  rw [h.2.2]
  exact Submodule.subset_span ⟨(j, k), rfl⟩

theorem eigCoord_mem (s : E →+* C) (v : Fin N → C) : eigCoord ρ t s v ∈ HT.eigSp ρ s := by
  rw [eigCoord_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ s _)

theorem exists_coord (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (h : HT.IsFreeOn ρ X t) {y : M} (hy : y ∈ X) :
    ∃ F : Fin N → (E →+* C) → w.valuationSubring, (∀ j, F j ∈ valSpan emb) ∧
      ∀ s, HT.eigProj ρ s y = ∑ j, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
  classical
  rw [h.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hx
    refine ⟨fun i s => if i = j then emb s (RingOfIntegers.basis E k) else 0, fun i => ?_,
      fun s => ?_⟩
    · by_cases hij : i = j
      · simp only [hij, if_true]
        exact Submodule.subset_span ⟨_, rfl⟩
      · simp only [hij, if_false]
        exact zero_mem (valSpan emb)
    · rw [HodgeDeterminantLattice.eigProj_act, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp [hemb]
  | zero => exact ⟨0, fun _ => zero_mem _, fun s => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    refine ⟨F + G, fun j => add_mem (hF j) (hG j), fun s => ?_⟩
    simp [e s, e' s, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    refine ⟨c • F, fun j => Submodule.smul_mem _ c (hF j), fun s => ?_⟩
    rw [← algebraMap_smul C c x, map_smul, e s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    rfl

theorem sum_smul_mem [CharZero C] [Fintype (E →+* C)]
    (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (hcard : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (h : HT.IsFreeOn ρ X t) (j : Fin N) {F : (E →+* C) → w.valuationSubring}
    (hF : F ∈ valSpan emb) :
    ∑ s, ((F s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X := by
  unfold valSpan at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have e : ∑ s : E →+* C, ((emb s a : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        ρ a (t j) := by
      have h1 := congrArg (fun T : Module.End C M => T (ρ a (t j)))
        (HT.sum_eigProj_eq_one C M E ρ hcard)
      simp only [LinearMap.sum_apply, HodgeDeterminantLattice.eigProj_act, Module.End.one_apply] at h1
      simpa only [hemb] using h1
    simpa only [e] using rho_mem h a j
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, AddMemClass.coe_add, add_smul, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ s : E →+* C, (((c • x) s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        c • ∑ s : E →+* C, ((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← algebraMap_smul C c (((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)), smul_smul]
      rfl
    rw [e]
    exact Submodule.smul_mem _ c hx

end

theorem block_freeLattice : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  intro E _ _ C _ _ w _ emb hemb hcard D π H M _ _ _ _ ρ X N t hfree _
  classical
  have hind : (fun s => if D s then (1 : w.valuationSubring) else 0) ∈ valSpan emb :=
    (H _ (fun s hs => if_neg hs)).1 ⟨1, fun s hs => by simp [hs]⟩
  have hpoly : ∀ F ∈ valSpan emb, ∃ g : Polynomial w.valuationSubring,
      ∀ s, D s → F s = g.eval (emb s π) := by
    intro F hF
    have hm := mul_mem_valSpan emb hind hF
    obtain ⟨g, hg⟩ := (H _ (fun s hs => by simp [hs])).2 hm
    exact ⟨g, fun s hs => by simpa [hs] using hg s hs⟩
  refine ⟨fun f => ⟨fun hx => ?_, fun hf => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hx
    have hD : ∀ s : {s // D s}, HT.eigProj ρ s.1 (∑ s, eigCoord ρ t s.1 (f s)) =
        eigCoord ρ t s.1 (f s) := by
      intro s
      rw [map_sum, Finset.sum_eq_single s]
      · exact HT.LatBasic.eigProj_of_mem (eigCoord_mem _ _)
      · intro s' _ hne
        exact HT.LatBasic.eigProj_of_ne (fun e => hne (Subtype.ext e.symm)) (eigCoord_mem _ _)
      · simp
    have hnD : ∀ s, ¬ D s → HT.eigProj ρ s (∑ s, eigCoord ρ t s.1 (f s)) = 0 := by
      intro s hs
      rw [map_sum]
      exact Finset.sum_eq_zero fun s' _ =>
        HT.LatBasic.eigProj_of_ne (fun e : s = s'.1 => hs (by rw [e]; exact s'.2)) (eigCoord_mem _ _)
    have hF0 : ∀ j s, ¬ D s → F j s = 0 := by
      intro j s hs
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s hfree)
        (fun j => ((F j s : w.valuationSubring) : C)) (by rw [← e s, hnD s hs]) j
      exact Subtype.ext h1
    have hcoord : ∀ (s : {s // D s}) j, f s j = ((F j s.1 : w.valuationSubring) : C) := by
      intro s j
      have h0 := (hD s).symm.trans (e s.1)
      rw [eigCoord_apply] at h0
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s.1 hfree)
        (fun j => f s j - ((F j s.1 : w.valuationSubring) : C))
        (by simp only [sub_smul, Finset.sum_sub_distrib, h0, sub_self]) j
      exact sub_eq_zero.1 h1
    refine mem_freeLattice.2 fun j => ?_
    obtain ⟨g, hg⟩ := (H (F j) (hF0 j)).2 (hF j)
    exact ⟨g, fun s => by rw [hcoord s j, hg s.1 s.2]⟩
  · choose g hg using mem_freeLattice.1 hf
    let F : Fin N → (E →+* C) → w.valuationSubring :=
      fun j s => if D s then (g j).eval (emb s π) else 0
    have hFm : ∀ j, F j ∈ valSpan emb := fun j =>
      (H (F j) (fun s hs => if_neg hs)).1 ⟨g j, fun s hs => if_pos hs⟩
    have key : ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X :=
      sum_mem fun j _ => sum_smul_mem emb hemb hcard hfree j (hFm j)
    have e : ∑ s, eigCoord ρ t s.1 (f s) =
        ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      simp only [eigCoord_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_eq_sum_subtype D _ (fun s hs => by simp [F, hs])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [F, if_pos s.2, hg j s]
    rw [e]
    exact key
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hy
    refine ⟨fun s j => ((F j s.1 : w.valuationSubring) : C), mem_freeLattice.2 fun j => ?_,
      fun s => ?_⟩
    · obtain ⟨g, hg⟩ := hpoly _ (hF j)
      exact ⟨g, fun s => by rw [hg s.1 s.2]⟩
    · rw [e, eigCoord_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_polynomial_vanishing_criterion : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice
end

section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_basis_split_of_exact_of_fg_valuationRing :
    ∀ (V C A W B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] [AddCommGroup A] [Module C A] [Module V A] [IsScalarTower V C A]
      [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [AddCommGroup B]
      [Module C B] [Module V B] [IsScalarTower V C B] (b : A →ₗ[C] W) (al : W →ₗ[C] B),
      Function.Injective b → Function.Exact b al → ∀ (T : Submodule V W), T.FG →
      ∃ (p q : ℕ) (w : Fin p → A) (t : Fin q → W), LinearIndependent C w ∧
        Submodule.span V (Set.range w) = T.comap (b.restrictScalars V) ∧
        LinearIndependent C (fun j => al (t j)) ∧
        Submodule.span V (Set.range fun j => al (t j)) = T.map (al.restrictScalars V) ∧
        LinearIndependent C (Sum.elim (fun i => b (w i)) t) ∧
        Submodule.span V (Set.range (Sum.elim (fun i => b (w i)) t)) = T := by
  intro V C A W B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b al hb hex T hT
  have : IsBezout V := ValuationRing.instIsBezout

  have hfree : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → Module.Free V N := by
    intro X _ _ _ _ N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    have : Module.Flat V N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
      have h2 : ((a : V) • x : N) = 0 := ha
      have h3 : (a : V) • (x : X) = 0 := by
        have h4 := congrArg Subtype.val h2
        simpa using h4
      have h1 : (algebraMap V C (a : V)) • (x : X) = 0 := by
        rw [algebraMap_smul]; exact h3
      have ha0 : algebraMap V C (a : V) ≠ 0 := by
        intro h
        have h5 : (a : V) = 0 := (IsFractionRing.injective V C) (by rw [h, map_zero])
        exact nonZeroDivisors.coe_ne_zero a h5
      have hx0 : (x : X) = 0 := (smul_eq_zero.mp h1).resolve_left ha0
      exact Subtype.ext (by simp [hx0])
    exact Module.free_of_flat_of_isLocalRing

  have hL : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → ∃ (n : ℕ) (v : Fin n → X),
        LinearIndependent C v ∧ Submodule.span V (Set.range v) = N := by
    intro X _ _ _ _ N hN
    have := hfree X N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    let e := (Module.Free.chooseBasis V N).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex V N))
    refine ⟨Fintype.card (Module.Free.ChooseBasisIndex V N), fun i => (e i : X), ?_, ?_⟩
    · rw [← LinearIndependent.iff_fractionRing V C]
      exact e.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    · have hr : Set.range (fun i => (e i : X)) = N.subtype '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [hr, Submodule.span_image, e.span_eq, Submodule.map_subtype_top]

  obtain ⟨q, u, hu, hus⟩ := hL B (T.map (al.restrictScalars V)) (hT.map _)
  have hu_mem : ∀ j, u j ∈ T.map (al.restrictScalars V) := by
    intro j
    rw [← hus]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose t ht hta using fun j => Submodule.mem_map.mp (hu_mem j)
  have hta' : ∀ j, al (t j) = u j := fun j => hta j
  have hal : (fun j => al (t j)) = u := funext hta'

  have : Module.Free V (T.map (al.restrictScalars V)) := hfree B _ (hT.map _)
  have : Module.Finite V (T.map (al.restrictScalars V)) := Module.Finite.iff_fg.mpr (hT.map _)
  have : Module.Finite V T := Module.Finite.iff_fg.mpr hT
  have : Module.FinitePresentation V (T.map (al.restrictScalars V)) :=
    Module.finitePresentation_of_projective V _
  have hker : (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).FG :=
    Module.FinitePresentation.fg_ker _ (LinearMap.submoduleMap_surjective _ _)
  have hK : (T.comap (b.restrictScalars V)).FG := by
    apply Submodule.fg_of_fg_map_injective (b.restrictScalars V) hb
    have heq : (T.comap (b.restrictScalars V)).map (b.restrictScalars V)
        = (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).map T.subtype := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨b a, ha⟩, ?_, rfl⟩
        show ((al.restrictScalars V).submoduleMap T) ⟨b a, ha⟩ = 0
        apply Subtype.ext
        show al (b a) = 0
        exact (hex (b a)).mpr ⟨a, rfl⟩
      · rintro ⟨⟨y, hyT⟩, hy0, rfl⟩
        have hy0' : ((al.restrictScalars V).submoduleMap T) ⟨y, hyT⟩ = 0 := hy0
        have hy : al y = 0 := congrArg Subtype.val hy0'
        obtain ⟨a, rfl⟩ := (hex y).mp hy
        exact ⟨a, hyT, rfl⟩
    rw [heq]
    exact hker.map _
  obtain ⟨p, w, hw, hws⟩ := hL A (T.comap (b.restrictScalars V)) hK
  refine ⟨p, q, w, t, hw, hws, ?_, ?_, ?_, ?_⟩
  · rw [hal]; exact hu
  · rw [hal]; exact hus
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have h1 : ∀ i, al (b (w i)) = 0 := fun i => (hex _).mpr ⟨w i, rfl⟩
    have h2 : ∑ j, g (Sum.inr j) • u j = 0 := by
      have h7 := congrArg al hg
      simpa [map_add, map_sum, map_smul, h1, hta'] using h7
    have h3 : ∀ j, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp hu (fun j => g (Sum.inr j)) h2
    have h4 : ∑ i, g (Sum.inl i) • b (w i) = 0 := by
      simpa [h3] using hg
    have h5 : ∑ i, g (Sum.inl i) • w i = 0 := by
      apply hb
      simpa [map_sum, map_smul] using h4
    have h6 := Fintype.linearIndependent_iff.mp hw (fun i => g (Sum.inl i)) h5
    intro i
    cases i with
    | inl i => exact h6 i
    | inr j => exact h3 j
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl i =>
        have hwi : w i ∈ T.comap (b.restrictScalars V) := by
          rw [← hws]; exact Submodule.subset_span ⟨i, rfl⟩
        exact hwi
      | inr j => exact ht j
    · intro x hx
      have hax : al x ∈ T.map (al.restrictScalars V) := Submodule.mem_map_of_mem hx
      rw [← hus, Submodule.mem_span_range_iff_exists_fun] at hax
      obtain ⟨c, hc⟩ := hax
      have hyal : al (x - ∑ j, c j • t j) = 0 := by
        rw [map_sub, map_sum]
        simp only [LinearMap.map_smul_of_tower, hta']
        rw [hc, sub_self]
      obtain ⟨a, ha⟩ := (hex _).mp hyal
      have haK : a ∈ T.comap (b.restrictScalars V) := by
        show b a ∈ T
        rw [ha]
        exact T.sub_mem hx (T.sum_mem fun j _ => T.smul_mem (c j) (ht j))
      rw [← hws] at haK
      have hx_eq : x = b a + ∑ j, c j • t j := by rw [ha]; abel
      rw [hx_eq, Set.Sum.elim_range, Submodule.span_union]
      apply Submodule.add_mem_sup
      · have hr : Set.range (fun i => b (w i)) = (b.restrictScalars V) '' Set.range w := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image]
        exact Submodule.mem_map_of_mem haK
      · exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_dual_integral_of_saturated_free_part :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W]
      [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W),
      Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w →
      (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) →
      ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧
        ∀ k, φ (w k) = if k = j then 1 else 0 := by
  intro V C _ _ _ _ _ _ W _ _ _ _ _ Lie n w hfg _ hw hsat j
  classical
  let W' : Submodule C W := Submodule.span C (Set.range w)
  obtain ⟨p, q, u, t, -, hu, ht, -, -, hspan⟩ :=
    exists_basis_split_of_exact_of_fg_valuationRing V C W' W (W ⧸ W') W'.subtype W'.mkQ
      W'.injective_subtype (LinearMap.exact_subtype_mkQ W') Lie hfg
  have hwW : ∀ i, w i ∈ W' := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hli : LinearIndependent C (Sum.elim w t) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    rw [Fintype.sum_sum_type] at hf
    simp only [Sum.elim_inl, Sum.elim_inr] at hf
    have h1 : ∀ i, f (Sum.inr i) = 0 := by
      have h := congrArg W'.mkQ hf
      have hz : ∀ i, W'.mkQ (w i) = 0 := fun i => by
        simpa using hwW i
      simp only [map_add, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, zero_add,
        map_zero] at h
      exact Fintype.linearIndependent_iff.mp ht _ h
    have h2 : ∀ i, f (Sum.inl i) = 0 := by
      simp only [h1, zero_smul, Finset.sum_const_zero, add_zero] at hf
      exact Fintype.linearIndependent_iff.mp hw _ hf
    rintro (i | i)
    · exact h2 i
    · exact h1 i
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination C (Sum.elim w t)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hli)
  have hgs : ∀ a, g (Sum.elim w t a) = Finsupp.single a 1 := fun a => by
    have h1 := LinearMap.congr_fun hg (Finsupp.single a 1)
    simpa [Finsupp.linearCombination_single] using h1
  let φ : Module.Dual C W := Finsupp.lapply (Sum.inl j) ∘ₗ g
  have hφw : ∀ k, φ (w k) = if k = j then 1 else 0 := fun k => by
    have h := hgs (Sum.inl k)
    simp only [Sum.elim_inl] at h
    simp [φ, h, Finsupp.single_apply]
  have hφt : ∀ i, φ (t i) = 0 := fun i => by
    have h := hgs (Sum.inr i)
    simp only [Sum.elim_inr] at h
    simp [φ, h, Finsupp.single_apply]
  let R : Submodule V C := LinearMap.range (Algebra.linearMap V C)
  have hone : (1 : C) ∈ R := ⟨1, by simp⟩
  have hzero : (0 : C) ∈ R := R.zero_mem
  have hspw : Submodule.span V (Set.range w) ≤ R.comap (φ.restrictScalars V) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change φ (w k) ∈ R
    rw [hφw]
    split_ifs
    · exact hone
    · exact hzero
  have hle : Lie ≤ R.comap (φ.restrictScalars V) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · apply hspw
      have hmem : u i ∈ Lie.comap (W'.subtype.restrictScalars V) := by
        rw [← hu]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact (hsat _).mpr ⟨hmem, (u i).2⟩
    · change φ (t i) ∈ R
      rw [hφt]
      exact hzero
  refine ⟨φ, fun y hy => ?_, hφw⟩
  obtain ⟨a, ha⟩ := hle hy
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_intersection_basis : ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W), Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w → (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) → ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil

section
variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {W : Type} [AddCommGroup W]
  [Module C W]

theorem eigProj_comp_bar [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C)
    (ρ : 𝓞 E →+* Module.End C W) (hsum : ∀ y, ∑ s, HT.eigProj ρ s y = y)
    (hσ : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (hbar : ∀ a, bar (bar a) = a) (x : W) :
    HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ x = HT.eigProj ρ σ' x := by
  classical
  conv_lhs => rw [← hsum x]
  rw [map_sum, Finset.sum_eq_single σ']
  · apply HT.LatBasic.eigProj_of_mem
    rw [HT.LatBasic.mem_eigSp]
    intro a
    have h := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ' x) (bar a)
    rw [hσ, hbar] at h
    exact h
  · intro s _ hs
    refine HT.LatBasic.eigProj_of_eigenSub_ne
      (χ := (s.comp (algebraMap (𝓞 E) E)).comp (bar : 𝓞 E →+* 𝓞 E)) ?_ ?_
    · intro e
      apply hs
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      refine RingHom.ext fun a => ?_
      have h := DFunLike.congr_fun e (bar a)
      have h2 : σ ((bar a : 𝓞 E) : E) = s (a : E) := by
        simpa [hbar] using h
      change s (a : E) = σ' (a : E)
      rw [hσ, h2]
    · rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ s x) (bar a)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eigProj_zero_form (bar : 𝓞 E ≃+* 𝓞 E) (σ : E →+* C) (ρ : 𝓞 E →+* Module.End C W)
    (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W))
    (hact : ∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) (φ : Module.Dual C W) :
    HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj (ρ.comp (bar : 𝓞 E →+* 𝓞 E)) σ) := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hact]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · ext x
    simp [Prod.snd_sum, LinearMap.sum_apply]

end

theorem span_iff_proj : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  intro E _ _ V C _ _ _ _ bar σ σ' W _ _ _ _ ρ ρH HV Lie n w ψ hsum hσ hbar _ hact hlat hspan hwL hψ hint y
  classical

  have hform : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = (0, φ ∘ₗ HT.eigProj ρ σ') := by
    intro φ
    rw [eigProj_zero_form bar σ ρ ρH hact φ]
    refine Prod.ext rfl ?_
    ext x
    simp only [LinearMap.comp_apply]
    rw [eigProj_comp_bar bar σ σ' ρ hsum hσ hbar x]
  have hψe : ∀ j, ψ j = (0, (ψ j).2) := fun j => Prod.ext (hψ j).2.1 rfl

  have hχ : ∀ j x, (ψ j).2 x = (ψ j).2 (HT.eigProj ρ σ' x) := by
    intro j x
    have h := HT.LatBasic.eigProj_of_mem (hψ j).1
    rw [hψe j, hform] at h
    have h2 := congrArg (fun z : W × Module.Dual C W => z.2 x) h
    exact h2.symm

  have hexp : ∀ x, HT.eigProj ρ σ' x = ∑ j, (ψ j).2 x • w j := by
    intro x
    have hm : HT.eigProj ρ σ' x ∈ Submodule.span C (Set.range w) := by
      rw [hspan]; exact HT.LatBasic.eigProj_mem ρ σ' x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hm
    have hcj : ∀ j, (ψ j).2 x = c j := by
      intro j
      rw [hχ j x, ← hc, map_sum]
      simp [(hψ j).2.2]
    simp only [hcj]
    exact hc.symm

  have key : ∀ φ : Module.Dual C W, HT.eigProj ρH σ (0, φ) = ∑ j, φ (w j) • ψ j := by
    intro φ
    rw [hform]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, (hψ _).2.1]
    · ext x
      simp only [LinearMap.comp_apply]
      rw [hexp x, map_sum, Prod.snd_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]

  have hsm : ∀ (v : V) (z : W × Module.Dual C W), v • z = algebraMap V C v • z := by
    intro v z
    refine Prod.ext ?_ ?_
    · simp
    · ext x
      simp [Algebra.smul_def]
  constructor
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hy
    choose φ hφ1 hφ2 using hint
    refine ⟨∑ j, algebraMap V C (c j) • φ j, ?_, ?_⟩
    · rw [hlat]
      intro e he
      rw [LinearMap.sum_apply]
      refine Subring.sum_mem _ fun j _ => ?_
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨c j, rfl⟩ (hφ1 j e he)
    · rw [key]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : (∑ j, algebraMap V C (c j) • φ j) (w k) = algebraMap V C (c k) := by
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hφ2, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsm, hk]
  · rintro ⟨φ, h0, rfl⟩
    rw [key]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨v, hv⟩ := (hlat φ).1 h0 (w j) (hwL j)
    rw [← hv, ← hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_dual_eigen_decomposition : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [Field C] [Algebra V C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (n : ℕ) (w : Fin n → W) (ψ : Fin n → W × Module.Dual C W), (∀ y, ∑ s, HT.eigProj ρ s y = y) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → Submodule.span C (Set.range w) = HT.eigSp ρ σ' → (∀ j, w j ∈ Lie) → (∀ j, ψ j ∈ HT.eigSp ρH σ ∧ (ψ j).1 = 0 ∧ ∀ j', (ψ j).2 (w j') = if j = j' then 1 else 0) → (∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0) → ∀ y, y ∈ Submodule.span V (Set.range ψ) ↔ ∃ φ : Module.Dual C W, ((0, φ) : W × Module.Dual C W) ∈ HV ∧ HT.eigProj ρH σ (0, φ) = y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualFil.span_iff_proj
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank

theorem comp_eigProj_eq {E : Type} [Field E] [NumberField E] {C : Type} [Field C]
    [Fintype (E →+* C)] {W : Type} [AddCommGroup W] [Module C W]
    {ρ : 𝓞 E →+* Module.End C W} {s' : E →+* C}
    (hsum : ∀ y, ∑ t, HT.eigProj ρ t y = y) {φ : Module.Dual C W}
    (hφ : ∀ a : 𝓞 E, φ ∘ₗ ρ a = s' (a : E) • φ) :
    φ ∘ₗ HT.eigProj ρ s' = φ := by
  classical
  ext y
  have key : ∀ t, t ≠ s' → φ (HT.eigProj ρ t y) = 0 := by
    intro t ht
    have hmem := HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ t y)
    have hex : ∃ a : 𝓞 E, t (a : E) ≠ s' (a : E) := by
      by_contra hc
      push_neg at hc
      exact ht (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hc))
    obtain ⟨a, ha⟩ := hex
    have h1 := LinearMap.congr_fun (hφ a) (HT.eigProj ρ t y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hmem a, map_smul, smul_eq_mul] at h1
    have h2 : (t (a : E) - s' (a : E)) * φ (HT.eigProj ρ t y) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
  have e : φ y = φ (HT.eigProj ρ s' y) := by
    conv_lhs => rw [← hsum y]
    rw [map_sum, Finset.sum_eq_single s' (fun t _ ht => key t ht) (by simp)]
  exact e.symm

theorem finrank_eigSp_inf_ker_fst :
    ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  intro E _ _ C _ _ bar s s' W _ _ _ ρ ρH hsum hs hbar hH
  set U := HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) with hU
  set T := HT.eigSp ρ s' with hT
  let F : U →ₗ[C] Module.Dual C T :=
    T.dualRestrict ∘ₗ LinearMap.snd C W (Module.Dual C W) ∘ₗ U.subtype
  have hFapply : ∀ (u : U) (x : T), F u x = (u : W × Module.Dual C W).2 x := fun _ _ => rfl
  have hfst : ∀ u : U, (u : W × Module.Dual C W).1 = 0 := fun u => u.2.2
  have hact : ∀ u : U, ∀ a : 𝓞 E,
      (u : W × Module.Dual C W).2 ∘ₗ ρ a = s' (a : E) • (u : W × Module.Dual C W).2 := by
    intro u a
    have h1 := HT.LatBasic.mem_eigSp.1 u.2.1 (bar a)
    have h2 : (u : W × Module.Dual C W) = (0, (u : W × Module.Dual C W).2) :=
      Prod.ext (hfst u) rfl
    rw [h2, hH, hbar] at h1
    have h3 := congrArg Prod.snd h1
    simpa [hs a] using h3
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 := comp_eigProj_eq hsum (hact u)
    apply Subtype.ext
    refine Prod.ext (hfst u) ?_
    rw [← h0]
    ext y
    have := hFapply u ⟨HT.eigProj ρ s' y, HT.LatBasic.eigProj_mem ρ s' y⟩
    rw [hu] at this
    simpa using this.symm
  have hsurj : Function.Surjective F := by
    intro ψ
    let e : W →ₗ[C] T := LinearMap.codRestrict T (HT.eigProj ρ s') (HT.LatBasic.eigProj_mem ρ s')
    have he : ∀ (b : 𝓞 E) (x : W), e (ρ b x) = s' (b : E) • e x := fun b x =>
      Subtype.ext (HodgeDeterminantLattice.eigProj_act s' b x)
    have hmem : ((0 : W), ψ ∘ₗ e) ∈ U := by
      refine ⟨HT.LatBasic.mem_eigSp.2 fun a => ?_, rfl⟩
      rw [hH]
      refine Prod.ext (by simp) ?_
      ext x
      simp [he, hs, hbar]
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    rw [hFapply]
    have : e x = x := Subtype.ext (HT.LatBasic.eigProj_of_mem x.2)
    simp [this]
  rw [(LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Subspace.dual_finrank_eq]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_module_conjugate_eigen_action : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core

section Lemmas

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {S W : Type} [AddCommGroup W] [Module C W]

theorem isFiltration_kerFil (a : S → w.valuationSubring) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) : IsFiltration a (kerFil a N g) where
  le := fun _ hx => hx.1
  stable := by
    rintro x ⟨hx, h0⟩
    refine ⟨fun i => ?_, fun s => ?_⟩
    · obtain ⟨f, hf⟩ := hx i
      exact ⟨Polynomial.X * f, fun s => by simp [unif, hf s]⟩
    · show g s ((a s : C) • x s) = 0
      rw [map_smul, h0 s, smul_zero]
  saturated := by
    rintro x hx c hc ⟨-, h0⟩
    refine ⟨hx, fun s => ?_⟩
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    have h1 := h0 s
    rw [show (c • x) s = (c : C) • x s from rfl, map_smul] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc'

theorem exists_clear_denom {N : ℕ} (y : Fin N → C) :
    ∃ c : w.valuationSubring, c ≠ 0 ∧ ∀ i, (c : C) * y i ∈ w.valuationSubring := by
  have h1 : ∀ i, ∃ c : w.valuationSubring, c ≠ 0 ∧ (c : C) * y i ∈ w.valuationSubring := by
    intro i
    rcases w.valuationSubring.mem_or_inv_mem (y i) with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · by_cases h0 : y i = 0
      · exact ⟨1, one_ne_zero, by simp [h0, zero_mem]⟩
      · refine ⟨⟨_, h⟩, fun e => h0 ?_, ?_⟩
        · simpa using congrArg (Subtype.val) e
        · simp [h0, one_mem]
  choose c hc hcy using h1
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
  push_cast
  rw [mul_comm (c i : C), mul_assoc]
  refine mul_mem ?_ (hcy i)
  exact_mod_cast (∏ j ∈ Finset.univ.erase i, c j).2

theorem filSpace_kerFil [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (N : ℕ) (g : S → (Fin N → C) →ₗ[C] W) (s : S) :
    filSpace (kerFil a N g) s = LinearMap.ker (g s) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf.2 s
  · intro y hy
    obtain ⟨c, hc, hcy⟩ := exists_clear_denom (w := w) y
    let Q : Polynomial w.valuationSubring :=
      ∏ t ∈ Finset.univ.erase s, (Polynomial.X - Polynomial.C (a t))
    have hQ0 : ∀ t, t ≠ s → Q.eval (a t) = 0 := by
      intro t ht
      simp only [Q, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨ht, Finset.mem_univ t⟩) (by simp)
    have hQ : Q.eval (a s) ≠ 0 := by
      simp only [Q, Polynomial.eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.2 fun e => (Finset.mem_erase.1 ht).1 (ha e).symm
    have hQ' : ((Q.eval (a s) : w.valuationSubring) : C) ≠ 0 := fun e => hQ (Subtype.ext e)
    have hc' : (c : C) ≠ 0 := fun e => hc (Subtype.ext e)
    let d : C := ((Q.eval (a s) : w.valuationSubring) : C) * c
    have hd : d ≠ 0 := mul_ne_zero hQ' hc'
    have hmem : d • y ∈ filSpace (kerFil a N g) s := by
      refine Submodule.subset_span (Submodule.mem_map.2 ⟨Pi.single s (d • y), ⟨fun i => ?_, fun t => ?_⟩, by simp⟩)
      · refine ⟨Polynomial.C ⟨_, hcy i⟩ * Q, fun t => ?_⟩
        by_cases ht : t = s
        · subst ht
          simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
            Polynomial.eval_C, d]
          push_cast
          ring
        · rw [Pi.single_eq_of_ne ht, Polynomial.eval_mul, hQ0 t ht]
          simp
      · by_cases ht : t = s
        · subst ht
          rw [Pi.single_eq_same, map_smul, LinearMap.mem_ker.1 hy, smul_zero]
        · rw [Pi.single_eq_of_ne ht, map_zero]
    have h2 := Submodule.smul_mem _ d⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2

variable [Fintype S] [DecidableEq S] [Module w.valuationSubring W]
  [IsScalarTower w.valuationSubring C W]

theorem mkQ_mem_eigenSub_iff (a : S → w.valuationSubring) (ha : Function.Injective a) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) (τ : S) (L : Submodule w.valuationSubring W)
    (hind : ∀ f : S → Fin N → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0)
    (hL : ∀ y, y ∈ L ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a N, ∑ s, g s (f s) = y)
    (z : Fin N → C) :
    (filSpace (kerFil a N g) τ).mkQ z ∈ eigenSub (lie (freeLattice a N) (kerFil a N g)) τ ↔
      g τ z ∈ L := by
  have hfs : ∀ (s : S) (x : Fin N → C), (filSpace (kerFil a N g) s).mkQ x = 0 ↔ g s x = 0 := by
    intro s x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, filSpace_kerFil a ha N g s,
      LinearMap.mem_ker]
  constructor
  · intro h
    obtain ⟨f, hf, e⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 h)
    have hs : ∀ s, s ≠ τ → g s (f s) = 0 := by
      intro s hs
      have h1 := congrFun e s
      rw [LinearMap.single_apply, Pi.single_eq_of_ne hs] at h1
      exact (hfs s _).1 h1
    have hτ : g τ (f τ) = g τ z := by
      have h1 := congrFun e τ
      rw [LinearMap.single_apply, Pi.single_eq_same] at h1
      have h2 : (filSpace (kerFil a N g) τ).mkQ (f τ - z) = 0 := by
        rw [map_sub, sub_eq_zero]; exact h1
      have h3 := (hfs τ _).1 h2
      rwa [map_sub, sub_eq_zero] at h3
    rw [hL]
    refine ⟨⟨z, rfl⟩, f, hf, ?_⟩
    rw [Finset.sum_eq_single τ (fun s _ h => hs s h) (by simp), hτ]
  · intro h
    obtain ⟨-, f, hf, e⟩ := (hL _).1 h
    have hu : ∀ s, g s (Function.update f τ (f τ - z) s) =
        g s (f s) - if s = τ then g τ z else 0 := by
      intro s
      by_cases hs : s = τ
      · subst hs; simp
      · simp [hs]
    have h0 := hind (Function.update f τ (f τ - z)) (by
      simp only [hu]
      rw [Finset.sum_sub_distrib, e]
      simp)
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨f, hf, funext fun s => ?_⟩)
    by_cases hs : s = τ
    · subst hs
      have h1 := h0 s
      rw [hu, if_pos rfl] at h1
      have h2 : (filSpace (kerFil a N g) s).mkQ (f s - z) = 0 := (hfs s _).2 (by rw [map_sub]; exact h1)
      rw [map_sub, sub_eq_zero] at h2
      rw [LinearMap.single_apply, Pi.single_eq_same]
      exact h2
    · have h1 := h0 s
      rw [hu, if_neg hs, sub_zero] at h1
      rw [LinearMap.single_apply, Pi.single_eq_of_ne hs]
      exact (hfs s _).2 h1

theorem isLatticeBasis_mkQ (a : S → w.valuationSubring) (ha : Function.Injective a) (N : ℕ)
    (g : S → (Fin N → C) →ₗ[C] W) (τ : S) {p : ℕ} (v : Fin p → W)
    (hind : ∀ f : S → Fin N → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0)
    (hv : LinearIndependent C v)
    (hL : ∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔
      y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a N, ∑ s, g s (f s) = y)
    (u : Fin p → Fin N → C) (hu : ∀ i, g τ (u i) = v i) :
    IsLatticeBasis w (fun i => (filSpace (kerFil a N g) τ).mkQ (u i))
      (eigenSub (lie (freeLattice a N) (kerFil a N g)) τ) := by
  have hfs : ∀ x : Fin N → C, (filSpace (kerFil a N g) τ).mkQ x = 0 ↔ g τ x = 0 := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, filSpace_kerFil a ha N g τ,
      LinearMap.mem_ker]
  have hmem := mkQ_mem_eigenSub_iff a ha N g τ _ hind hL
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : g τ (∑ i, c i • u i) = 0 := (hfs _).1 (by
      rw [map_sum]
      simpa only [map_smul] using hc)
    rw [map_sum] at h1
    simp only [map_smul, hu] at h1
    exact Fintype.linearIndependent_iff.1 hv c h1
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (hmem _).2 (by rw [hu]; exact Submodule.subset_span ⟨i, rfl⟩)
    · intro zq hz
      obtain ⟨z, rfl⟩ := (filSpace (kerFil a N g) τ).mkQ_surjective zq
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1
        ((hmem z).1 hz)
      have h0 : (filSpace (kerFil a N g) τ).mkQ (z - ∑ i, (c i : C) • u i) = 0 := (hfs _).2 (by
        rw [map_sub, map_sum, sub_eq_zero, ← hc]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hu]
        exact (algebraMap_smul C (c i) (v i)).symm)
      rw [map_sub, sub_eq_zero, map_sum] at h0
      rw [h0]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      rw [show (c i : C) • (filSpace (kerFil a N g) τ).mkQ (u i) =
        c i • (filSpace (kerFil a N g) τ).mkQ (u i) from algebraMap_smul C (c i) _]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Lemmas

theorem exists_unit_of_val_eq {C : Type} [Field C] {w : Valuation C ℝ≥0} {x y : C} (hy : y ≠ 0)
    (h : w x = w y) : ∃ ε : (w.valuationSubring)ˣ, x = (ε : w.valuationSubring) * y := by
  have hwy : w y ≠ 0 := (w.ne_zero_iff).2 hy
  have hx : x ≠ 0 := (w.ne_zero_iff).1 (h ▸ hwy)
  have ht : x / y ≠ 0 := div_ne_zero hx hy
  have h1 : w (x / y) = 1 := by rw [map_div₀, h, div_self hwy]
  have h2 : w (x / y)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  refine ⟨⟨⟨x / y, (w.mem_valuationSubring_iff _).2 h1.le⟩,
    ⟨(x / y)⁻¹, (w.mem_valuationSubring_iff _).2 h2.le⟩,
    Subtype.ext (mul_inv_cancel₀ ht), Subtype.ext (inv_mul_cancel₀ ht)⟩, ?_⟩
  show x = x / y * y
  rw [div_mul_cancel₀ _ hy]

theorem det_adapted_core : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (τ : S) (r : S → ℕ) (W : Type) [AddCommGroup W] [Module C W] [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] (g : S → (Fin (p + q) → C) →ₗ[C] W) (v : Fin p → W) (U : Fin (p + q) → Fin (p + q) → C) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), Function.Injective a → (∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0) → (∀ s, Module.finrank C (LinearMap.ker (g s)) = r s) → r τ = q → LinearIndependent C v → (∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y) → (∀ i, g τ (U (Fin.castAdd q i)) = v i) → (∀ j, g τ (U (Fin.natAdd p j)) = 0) → IsLatticeBasis w (fun j => U (Fin.natAdd p j)) (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) → IsLatticeBasis w (fun i => ∑ j, A i j • U j) (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) → ∃ ε : (w.valuationSubring)ˣ, A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q) = (ε : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q τ r W _ _ _ _ g v U A ha hind hrank hrq hv hspan hU1 hU2 hM hX
  have hFil := isFiltration_kerFil a (p + q) g
  have hLie := isLatticeBasis_mkQ a ha (p + q) g τ v hind hv hspan
    (fun i => U (Fin.castAdd q i)) hU1
  obtain ⟨c, hc, hdet⟩ := GlobalTheory.FrameModel.det_append_eq_mul_det C w ℓ hℓ0 hℓ1 S a p q
    (kerFil a (p + q) g) τ ha hFil _ _ _ hX hLie hM
  have happ : Fin.append (fun i => U (Fin.castAdd q i)) (fun j => U (Fin.natAdd p j)) = U := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
  have hx : Matrix.of (fun i => ∑ j, A i j • U j) = A * Matrix.of U := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [happ, hx, Matrix.det_mul] at hdet
  have hAU : (A * Matrix.of U).det ≠ 0 := by
    have hu : IsUnit (Matrix.of (fun i => ∑ j, A i j • U j)) :=
      Matrix.linearIndependent_rows_iff_isUnit.1 hX.1
    rw [hx] at hu
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hU0 : (Matrix.of U).det ≠ 0 := by
    rw [Matrix.det_mul] at hAU
    exact right_ne_zero_of_mul hAU
  have hcA : c * A.det = 1 := by
    have h1 : (c * A.det) * (Matrix.of U).det = 1 * (Matrix.of U).det := by
      rw [one_mul, mul_assoc]; exact hdet.symm
    exact mul_right_cancel₀ hU0 h1
  have hne : ∀ s ∈ Finset.univ.erase τ, (a τ : C) - (a s : C) ≠ 0 := fun s hs e =>
    (Finset.mem_erase.1 hs).1 (ha (Subtype.ext (sub_eq_zero.1 e))).symm
  have hr : ∀ s, Module.finrank C (filSpace (kerFil a (p + q) g) s) = r s := fun s => by
    rw [filSpace_kerFil a ha (p + q) g s, hrank s]
  have hle : ∀ s, r s ≤ p + q := fun s => by
    rw [← hr s]
    simpa using Submodule.finrank_le (filSpace (kerFil a (p + q) g) s)
  have hval : w (A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q)) =
      w (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s) := by
    have hwc : w c * w A.det = 1 := by rw [← map_mul, hcA, map_one]
    have hsplit : w ((∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q)) =
        w c * w (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s) := by
      simp only [hr] at hc
      rw [hc, map_pow, map_prod, map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_pow, ← pow_add, Nat.sub_add_cancel (hle s)]
    rw [map_mul, hsplit, ← mul_assoc, mul_comm (w A.det), hwc, one_mul]
  exact exists_unit_of_val_eq (Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hne s hs)) hval

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lattice_matrix_reduction : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (τ : S) (r : S → ℕ) (W : Type) [AddCommGroup W] [Module C W] [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] (g : S → (Fin (p + q) → C) →ₗ[C] W) (v : Fin p → W) (U : Fin (p + q) → Fin (p + q) → C) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), Function.Injective a → (∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0) → (∀ s, Module.finrank C (LinearMap.ker (g s)) = r s) → r τ = q → LinearIndependent C v → (∀ y, y ∈ Submodule.span w.valuationSubring (Set.range v) ↔ y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y) → (∀ i, g τ (U (Fin.castAdd q i)) = v i) → (∀ j, g τ (U (Fin.natAdd p j)) = 0) → IsLatticeBasis w (fun j => U (Fin.natAdd p j)) (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) → IsLatticeBasis w (fun i => ∑ j, A i j • U j) (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) → ∃ ε : (w.valuationSubring)ˣ, A.det * (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))) ^ (p + q) = (ε : w.valuationSubring) * ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.Core.det_adapted_core
end

section
section
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red

section Xfer

variable {A B K M : Type} [CommRing A] [CommRing B] [CommRing K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]

def xfer (h : (algebraMap A K).range = (algebraMap B K).range) (X : Submodule A M) : Submodule B M where
  carrier := X
  zero_mem' := X.zero_mem
  add_mem' := fun hx hy => X.add_mem hx hy
  smul_mem' := fun c x hx => by
    obtain ⟨a, ha⟩ : algebraMap B K c ∈ (algebraMap A K).range := h ▸ ⟨c, rfl⟩
    have e : c • x = a • x := by rw [← algebraMap_smul K c x, ← ha, algebraMap_smul]
    rw [e]
    exact X.smul_mem a hx

theorem mem_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {X : Submodule A M} {y : M} :
    y ∈ xfer h X ↔ y ∈ X := Iff.rfl

theorem xfer_span (h : (algebraMap A K).range = (algebraMap B K).range) (s : Set M) :
    xfer h (Submodule.span A s) = Submodule.span B s := by
  apply le_antisymm
  · intro y hy
    exact (Submodule.span_le (p := xfer h.symm (Submodule.span B s))).2
      (fun z hz => Submodule.subset_span hz) hy
  · exact Submodule.span_le.2 fun z hz => Submodule.subset_span hz

end Xfer

section XferEig

variable {A B K M : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]
  [AddCommGroup M] [Module K M] [Module A M] [Module B M] [IsScalarTower A K M] [IsScalarTower B K M]
  {E : Type} [Field E] [NumberField E]

theorem xfer_eigSub (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigSub ρ σ X) = HT.eigSub ρ σ (xfer h X) := by
  ext y
  exact Iff.rfl

theorem xfer_eigQuot (h : (algebraMap A K).range = (algebraMap B K).range) (ρ : 𝓞 E →+* Module.End K M) (σ : E →+* K)
    (X : Submodule A M) : xfer h (HT.eigQuot ρ σ X) = HT.eigQuot ρ σ (xfer h X) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isFreeOn_xfer (h : (algebraMap A K).range = (algebraMap B K).range) {ρ : 𝓞 E →+* Module.End K M}
    {X : Submodule A M} {N : ℕ} {t : Fin N → M} (hf : HT.IsFreeOn ρ X t) :
    HT.IsFreeOn ρ (xfer h X) t := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  rw [← xfer_span h, ← hf.2.2]

end XferEig

theorem targetV : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  intro hO E _ _ V C _ _ _ _ _ _ _ bar σ σ' rk p q ν hν hℓ hs hcard hσ' hbar
  have hr : (algebraMap V C).range = (algebraMap ν.valuationSubring C).range := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨_, (Valuation.mem_valuationSubring_iff _ _).2 (hν.map_le_one a)⟩, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨a, ha⟩ := hν.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 o.2)
      exact ⟨a, ha⟩
  obtain ⟨γ, hγ, H⟩ := hO E C ν bar σ σ' rk p q hℓ (fun s a => by
    obtain ⟨o, ho⟩ : s (a : E) ∈ (algebraMap ν.valuationSubring C).range := hr ▸ hs s a
    rw [← ho]
    exact o.2) hcard hσ' hbar
  refine ⟨γ, hγ, ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  letI : Module ν.valuationSubring W := Module.compHom W (algebraMap ν.valuationSubring C)
  haveI : IsScalarTower ν.valuationSubring C W := ⟨fun o c y => by
    change ((o : C) * c) • y = (o : C) • (c • y)
    rw [mul_smul]⟩
  obtain ⟨ε, hε⟩ := H W ρ ρH (xfer hr HV) (xfer hr Lie) x v w u A h1 h2
    (by
      ext y
      rw [mem_xfer, ← h3]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩)
    (fun φ => by
      rw [mem_xfer, h4, ← hr]
      exact Iff.rfl)
    (isFreeOn_xfer hr h5) h6 h7
    (by rw [← xfer_span hr, h8, xfer_eigSub]) h9
    (by rw [← xfer_span hr, h10, xfer_eigSub]) h11 h12
    (by rw [← xfer_span hr, h13, xfer_eigQuot])
  obtain ⟨a, ha⟩ : algebraMap ν.valuationSubring C (ε : ν.valuationSubring) ∈ (algebraMap V C).range :=
    hr ▸ ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : algebraMap ν.valuationSubring C ((ε⁻¹ : (ν.valuationSubring)ˣ) : ν.valuationSubring) ∈
      (algebraMap V C).range := hr ▸ ⟨_, rfl⟩
  have hab : a * b = 1 := by
    apply hν.hom_inj
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ?_⟩
  rw [hε]
  exact congrArg (· * γ) ha.symm

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red
end
end

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_valuation_rank_bound : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV
end

section
section
open scoped NNReal
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem targetO : TargetO := by
  intro E _ _ C _ _ ν bar σ σ' rk p q hℓ hint hcard hσ' hbar
  classical
  obtain ⟨ℓ, h0, h1⟩ := hℓ
  haveI : Finite (E →+* C) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* C) := Fintype.ofFinite _
  have hcard' : Fintype.card (E →+* C) = Module.finrank ℚ E := by rw [← Nat.card_eq_fintype_card, hcard]
  have hsumAll := GlobalTheory.T.sum_eigen_projections_eq_self E C hcard'
  let emb : (E →+* C) → (𝓞 E →+* ν.valuationSubring) := fun s =>
    (s.comp (algebraMap (𝓞 E) E)).codRestrict ν.valuationSubring (fun a => hint s a)
  have hemb : ∀ s (a : 𝓞 E), ((emb s a : ν.valuationSubring) : C) = s (a : E) := fun s a => rfl
  obtain ⟨π, hπ1, hπ2⟩ := GlobalTheory.T.statement_unavailable_one E ν.valuationSubring C emb (fun s a => hemb s a) hcard σ
  let D : (E →+* C) → Prop := fun s => ∀ a, ¬ IsUnit (emb s a - emb σ a)
  let S := {s // D s}
  have hDσ : D σ := fun a => by simp
  let τ : S := ⟨σ, hDσ⟩
  let a : S → ν.valuationSubring := fun s => emb s.1 π
  have ha : Function.Injective a := fun s s' e => Subtype.ext (hπ1 _ _ s.2 s'.2 e)
  have hmono : ∀ f : (E →+* C) → ν.valuationSubring, (∀ s, ¬ D s → f s = 0) →
      ((∃ g : Polynomial ν.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔
        f ∈ Submodule.span ν.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
    intro f hf
    refine hπ2 f (fun s hs => hf s ?_)
    intro hd
    obtain ⟨b, hb⟩ := hs
    exact hd b hb

  have hbarE : ∀ s : E →+* C, ∃ s' : E →+* C, ∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E) := by
    intro s
    have hinj : Function.Injective ((s.comp (algebraMap (𝓞 E) E)).comp bar.toRingHom) := by
      refine (s.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)).comp bar.injective
    exact ⟨IsFractionRing.lift hinj, fun a => IsFractionRing.lift_algebraMap hinj a⟩
  choose sbar hsbar using hbarE
  let r : S → ℕ := fun s => rk (sbar s.1)
  let P : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))
  have hne : ∀ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ≠ 0 := by
    intro s hs e
    have : a τ = a s := Subtype.ext (sub_eq_zero.1 e)
    exact (Finset.mem_erase.1 hs).1 (ha this).symm
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 hne
  let Q : C := ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) ^ r s
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun s hs => pow_ne_zero _ (hne s hs)
  refine ⟨Q / P ^ (p + q), div_ne_zero hQ (pow_ne_zero _ hP), ?_⟩
  intro W _ _ _ _ _ ρ ρH HV Lie x v w u A hfst hinr hmap hfil hfree hrk hv hvs hw hws had hAl hAs
  have hIv : ν.Integers ν.valuationSubring :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => x.2
      exists_of_le_one := fun {r} h => ⟨⟨r, h⟩, rfl⟩ }
  have hsumW := hsumAll W ρ
  have hsumH := hsumAll _ ρH

  have fstE : ∀ (s : E →+* C) (y : W × Module.Dual C W), (HT.eigProj ρH s y).1 = HT.eigProj ρ s y.1 := by
    intro s y
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, hfst]
  let T : S → (Fin (p + q) → C) →ₗ[C] (W × Module.Dual C W) := fun s => eigCoord ρH x s.1
  let g : S → (Fin (p + q) → C) →ₗ[C] W := fun s => (LinearMap.fst C W (Module.Dual C W)) ∘ₗ T s
  have hgT : ∀ s y, g s y = (T s y).1 := fun s y => rfl
  have Tmem : ∀ s y, T s y ∈ HT.eigSp ρH s.1 := by
    intro s y
    change eigCoord ρH x s.1 y ∈ _
    rw [eigCoord_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem _ _ _)
  have gmem : ∀ s y, g s y ∈ HT.eigSp ρ s.1 := by
    intro s y
    rw [HT.LatBasic.mem_eigSp]
    intro b
    rw [hgT, ← hfst, HT.LatBasic.mem_eigSp.1 (Tmem s y) b]
    rfl
  have Tinj : ∀ s, Function.Injective (T s) := by
    intro s
    have hli := HodgeDeterminantLattice.linearIndependent_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    change eigCoord ρH x s.1 y = 0 at hy
    rw [eigCoord_apply] at hy
    exact funext (Fintype.linearIndependent_iff.1 hli y hy)
  have Tsurj : ∀ s y, y ∈ HT.eigSp ρH s.1 → ∃ z, T s z = y := by
    intro s y hy
    have hsp := HodgeDeterminantLattice.span_eigProj (A := ν.valuationSubring) s.1 hfree
    rw [← hsp] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 hy
    exact ⟨c, by change eigCoord ρH x s.1 c = y; rw [eigCoord_apply]; exact hc⟩

  have projSum : ∀ (f : S → Fin (p + q) → C) (t : S), HT.eigProj ρH t.1 (∑ s, T s (f s)) = T t (f t) := by
    intro f t
    rw [map_sum, Finset.sum_eq_single t]
    · exact HT.LatBasic.eigProj_of_mem (Tmem _ _)
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (Tmem _ _)
    · simp
  have hind : ∀ f : S → Fin (p + q) → C, ∑ s, g s (f s) = 0 → ∀ s, g s (f s) = 0 := by
    intro f hf t
    have h2 := congrArg (HT.eigProj ρ t.1) hf
    rw [map_sum, map_zero, Finset.sum_eq_single t] at h2
    · rwa [HT.LatBasic.eigProj_of_mem (gmem _ _)] at h2
    · intro s _ hs
      exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e).symm) (gmem _ _)
    · simp
  have hblk := GlobalTheory.T.cm_type_polynomial_vanishing_criterion E C ν emb (fun s a => hemb s a) hcard' D π hmono _ ρH HV (p + q) x hfree
  obtain ⟨hb1, hb2⟩ := hblk
  have sumFst : ∀ f : S → Fin (p + q) → C, (∑ s, T s (f s)).1 = ∑ s, g s (f s) := by
    intro f
    exact map_sum (LinearMap.fst C W (Module.Dual C W)) _ _

  have hr : ∀ s, Module.finrank C (LinearMap.ker (g s)) = r s := by
    intro s
    have e1 : (LinearMap.ker (g s)).map (T s) =
        HT.eigSp ρH s.1 ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Tmem s z, hz⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨z, rfl⟩ := Tsurj s y h1
        exact ⟨z, h2, rfl⟩
    change _ = rk (sbar s.1)
    rw [← hrk, ← GlobalTheory.T.dual_module_conjugate_eigen_action E C bar s.1 (sbar s.1) W ρ ρH hsumW (hsbar s.1) hbar hinr, ← e1]
    exact (Submodule.equivMapOfInjective _ (Tinj s) _).finrank_eq
  have hspanLie : Submodule.span C (Lie : Set W) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have h3 : ((y, 0) : W × Module.Dual C W) ∈ Submodule.span C (HV : Set (W × Module.Dual C W)) := by
      rw [hfree.2.1]; trivial
    have h4 : ∀ z ∈ Submodule.span C (HV : Set (W × Module.Dual C W)), z.1 ∈ Submodule.span C (Lie : Set W) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (hmap ▸ ⟨z, hz, rfl⟩)
      | zero => exact zero_mem _
      | add z z' _ _ h h' => exact add_mem h h'
      | smul c z _ h => exact Submodule.smul_mem _ c h
    exact h4 _ h3
  have hLieFG : Lie.FG := by
    rw [← hmap, hfree.2.2]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  have hwLie : ∀ j, w j ∈ Lie ∧ w j ∈ HT.eigSp ρ σ' := by
    intro j
    have : w j ∈ HT.eigSub ρ σ' Lie := hws ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hwsp : Submodule.span C (Set.range w) = HT.eigSp ρ σ' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hwLie j).2
    · intro y hy
      obtain ⟨c, hc, hcy⟩ := HT.LatBasic.exists_smul_mem ν hIv (L := Lie) (x := y) (by rw [hspanLie]; trivial)
      have h3 : c • y ∈ HT.eigSub ρ σ' Lie := ⟨hcy, Submodule.smul_mem _ c hy⟩
      rw [← hws] at h3
      have h4 : c • y ∈ Submodule.span C (Set.range w) :=
        Submodule.span_le_restrictScalars ν.valuationSubring C _ h3
      have := Submodule.smul_mem _ c⁻¹ h4
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hsat : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w) := by
    intro y
    rw [hws, hwsp]
    exact Iff.rfl
  have hφ := GlobalTheory.T.lattice_span_intersection_basis ν.valuationSubring C W Lie q w hLieFG hspanLie hw hsat
  have hσbar : sbar σ = σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    (RingHom.ext fun b => (hsbar σ b).trans (hσ' b).symm)
  have hrτ : r τ = q := by
    change rk (sbar σ) = q
    rw [hσbar, ← hrk, ← hwsp, finrank_span_eq_card hw, Fintype.card_fin]

  have hex : ∀ i, ∃ z, T τ z = u i := fun i => Tsurj τ _ (had.1 i)
  choose U hU using hex
  have hU1 : ∀ i, g τ (U (Fin.castAdd q i)) = v i := fun i => by
    rw [hgT, hU]; exact had.2.1 i
  have hU2 : ∀ j, g τ (U (Fin.natAdd p j)) = 0 := fun j => by
    rw [hgT, hU]; exact (had.2.2 j).1
  have hTmemSpan : ∀ (n : ℕ) (b : Fin n → Fin (p + q) → C) (z : Fin (p + q) → C),
      z ∈ Submodule.span ν.valuationSubring (Set.range b) ↔
        T τ z ∈ Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) := by
    intro n b z
    have e : Submodule.span ν.valuationSubring (Set.range fun i => T τ (b i)) =
        (Submodule.span ν.valuationSubring (Set.range b)).map ((T τ).restrictScalars ν.valuationSubring) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e]
    constructor
    · exact fun h => ⟨z, h, rfl⟩
    · rintro ⟨z', h, e'⟩
      rwa [← Tinj τ e']
  have hLB2 : IsLatticeBasis ν (fun j => U (Fin.natAdd p j))
      (eigenQuot (W := fun _ => Fin (p + q) → C) (kerFil a (p + q) g) τ) := by
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h2 := congrArg (fun y : W × Module.Dual C W => y.2 (w k)) hc
      simp only [Function.comp, hU, Prod.snd_sum, Prod.smul_snd, LinearMap.sum_apply, LinearMap.smul_apply,
        (had.2.2 _).2, Prod.snd_zero, LinearMap.zero_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h2
      simpa using h2
    · ext z
      rw [hTmemSpan]
      simp only [hU]
      rw [GlobalTheory.T.hodge_lattice_dual_eigen_decomposition E ν.valuationSubring C bar σ σ' W ρ ρH HV Lie q w (fun j => u (Fin.natAdd p j)) hsumW hσ' hbar hfst hinr
        hfil hwsp (fun j => (hwLie j).1) (fun j => ⟨had.1 _, (had.2.2 j).1, (had.2.2 j).2⟩) hφ]
      constructor
      · rintro ⟨φ, h1, h2⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ h1
        refine ⟨f, ⟨hf, fun s => ?_⟩, ?_⟩
        · rw [hgT]
          change (eigCoord ρH x s.1 (f s)).1 = 0
          rw [← hfs, fstE]
          simp
        · apply Tinj τ
          rw [← h2, hfs τ]
          rfl
      · rintro ⟨f, ⟨hf, hg0⟩, rfl⟩
        have h3 := (hb1 f).2 hf
        have h4 : (∑ s, T s (f s)).1 = 0 := by
          rw [sumFst]
          exact Finset.sum_eq_zero fun s _ => hg0 s
        refine ⟨(∑ s, T s (f s)).2, ?_, ?_⟩
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact h3
        · have : ((0, (∑ s, T s (f s)).2) : W × Module.Dual C W) = ∑ s, T s (f s) := Prod.ext h4.symm rfl
          rw [this]
          exact projSum f τ
  have hvs' : ∀ y, y ∈ Submodule.span ν.valuationSubring (Set.range v) ↔
      y ∈ LinearMap.range (g τ) ∧ ∃ f ∈ freeLattice a (p + q), ∑ s, g s (f s) = y := by
    intro y
    rw [hvs]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy2' : y ∈ HT.eigSp ρ σ := hy2
      rw [← hmap] at hy1
      obtain ⟨η, hη, rfl⟩ := hy1
      change η.1 ∈ HT.eigSp ρ σ at hy2'
      obtain ⟨z, hz⟩ := Tsurj τ _ (HT.LatBasic.eigProj_mem ρH σ η)
      obtain ⟨f, hf, hfs⟩ := hb2 _ hη
      refine ⟨⟨z, ?_⟩, f, hf, ?_⟩
      · change (T τ z).1 = η.1
        rw [hz, fstE]
        exact HT.LatBasic.eigProj_of_mem hy2'
      · have h5 : ∀ s, g s (f s) = HT.eigProj ρ s.1 η.1 := fun s => by
          rw [hgT, ← fstE, hfs s]
        simp only [h5]
        rw [Finset.sum_eq_single τ]
        · exact HT.LatBasic.eigProj_of_mem hy2'
        · intro s _ hs
          exact HT.LatBasic.eigProj_of_ne (fun e => hs (Subtype.ext e)) hy2'
        · simp
    · rintro ⟨⟨z, rfl⟩, f, hf, e⟩
      refine ⟨?_, gmem τ z⟩
      rw [← hmap]
      exact ⟨_, (hb1 f).2 hf, (sumFst f).trans e⟩
  have hLBA : IsLatticeBasis ν (fun i => ∑ j, A i j • U j)
      (eigenQuot (W := fun _ => Fin (p + q) → C) (freeLattice a (p + q)) τ) := by
    have hTA : ∀ i, T τ (∑ j, A i j • U j) = ∑ j, A i j • u j := fun i => by
      simp only [map_sum, map_smul, hU]
    refine ⟨?_, ?_⟩
    · apply LinearIndependent.of_comp (T τ)
      have : (T τ) ∘ (fun i => ∑ j, A i j • U j) = fun i => ∑ j, A i j • u j := funext hTA
      rw [this]
      exact hAl
    · ext z
      rw [hTmemSpan]
      simp only [hTA]
      rw [hAs]
      constructor
      · rintro ⟨η, hη, e⟩
        obtain ⟨f, hf, hfs⟩ := hb2 _ hη
        refine ⟨f, hf, ?_⟩
        apply Tinj τ
        have e' : HT.eigProj ρH σ η = T τ z := e
        rw [← e', hfs τ]
        rfl
      · rintro ⟨f, hf, rfl⟩
        exact ⟨_, (hb1 f).2 hf, projSum f τ⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.T.valuation_lattice_matrix_reduction C ν ℓ h0 h1 S a p q τ r W g v U A ha hind hr hrτ hv hvs' hU1 hU2 hLB2 hLBA
  refine ⟨ε, ?_⟩
  change A.det * P ^ (p + q) = _ * Q at hε
  change A.det = ((ε : ν.valuationSubring) : C) * (Q / P ^ (p + q))
  rw [← mul_div_assoc, ← hε, mul_div_cancel_right₀ _ (pow_ne_zero _ hP)]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_adapted_eq_unit_mul_const : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ :=
  GlobalTheory.T.conjugate_embeddings_valuation_rank_bound ExG.targetO

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_valuation_embedding : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.det_adapted_eq_unit_mul_const
end
