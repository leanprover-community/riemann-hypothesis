import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlices
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesOver
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_restriction : GlobalTheory.CompanionTheory.EGlue.PairRestrict := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.pairRestrict_holds
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_fd_slices (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) :
    ∃ (A : Submodule ℂ (Sm E a)) (B : Submodule ℂ (Sm E b)), FiniteDimensional ℂ A ∧ FiniteDimensional ℂ B ∧
      (∀ m₂ : GA E b, ∃ φ ∈ A, φ.1 = fun x => F (x, m₂)) ∧ (∀ m₁ : GA E a, ∃ φ ∈ B, φ.1 = fun x => F (m₁, x)) := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, -, rfl⟩ := h
    refine ⟨Submodule.span ℂ {φ₁}, Submodule.span ℂ {φ₂}, inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · refine ⟨φ₂.1 m₂ • φ₁, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp [mul_comm]
    · refine ⟨φ₁.1 m₁ • φ₂, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
      funext x
      simp
  | zero =>
    refine ⟨⊥, ⊥, inferInstance, inferInstance, fun m₂ => ⟨0, Submodule.zero_mem _, ?_⟩,
      fun m₁ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · funext x
      simp
    · funext x
      simp
  | add F G _ _ hF hG =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    obtain ⟨A', B', hA', hB', h₁', h₂'⟩ := hG
    refine ⟨A ⊔ A', B ⊔ B', inferInstance, inferInstance, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      obtain ⟨φ', hφ', e'⟩ := h₁' m₂
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      obtain ⟨φ', hφ', e'⟩ := h₂' m₁
      refine ⟨φ + φ', Submodule.add_mem_sup hφ hφ', ?_⟩
      funext x
      simp [e, e']
  | smul c F _ hF =>
    obtain ⟨A, B, hA, hB, h₁, h₂⟩ := hF
    refine ⟨A, B, hA, hB, fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨φ, hφ, e⟩ := h₁ m₂
      refine ⟨c • φ, A.smul_mem c hφ, ?_⟩
      funext x
      simp [e]
    · obtain ⟨φ, hφ, e⟩ := h₂ m₁
      refine ⟨c • φ, B.smul_mem c hφ, ?_⟩
      funext x
      simp [e]

theorem pairFD_holds : PairFD := by
  intro E _ _ _ a b ι _ U₁ U₂ f hf
  choose A B hA hB h₁ h₂ using fun i => exists_fd_slices U₁ U₂ (f i) (hf i)
  have hA' : FiniteDimensional ℂ (⨆ i, A i : Submodule ℂ (Sm E a)) := Submodule.finiteDimensional_iSup A
  have hB' : FiniteDimensional ℂ (⨆ i, B i : Submodule ℂ (Sm E b)) := Submodule.finiteDimensional_iSup B
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, A i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₂, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₁ i m₂
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, B i) (Submodule.span_le.2 ?_)
    rintro φ ⟨i, m₁, e⟩
    obtain ⟨ψ, hψ, e'⟩ := h₂ i m₁
    have : φ = ψ := Subtype.ext (e.trans e'.symm)
    rw [this]
    exact Submodule.mem_iSup_of_mem i hψ

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_finite_dimensional : GlobalTheory.CompanionTheory.EGlue.PairFD := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.pairFD_holds
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.SliceTypePf

theorem restrict_left {A B : Type} [One B] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : A => f (k, 1)) ∈ W₁ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, h₁, w₂, -, rfl⟩ := h
    have : (fun k : A => w₁ k * w₂ 1) = w₂ 1 • w₁ := by
      funext k
      simp [mul_comm]
    simpa [this] using W₁.smul_mem _ h₁
  | zero => exact W₁.zero_mem
  | add f g _ _ hf hg => exact W₁.add_mem hf hg
  | smul c f _ hf => exact W₁.smul_mem c hf

theorem restrict_right {A B : Type} [One A] (W₁ : Submodule ℂ (A → ℂ)) (W₂ : Submodule ℂ (B → ℂ)) (f : A × B → ℂ)
    (hf : f ∈ Submodule.span ℂ {f : A × B → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :
    (fun k : B => f (1, k)) ∈ W₂ := by
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨w₁, -, w₂, h₂, rfl⟩ := h
    have : (fun k : B => w₁ 1 * w₂ k) = w₁ 1 • w₂ := by
      funext k
      simp
    simpa [this] using W₂.smul_mem _ h₂
  | zero => exact W₂.zero_mem
  | add f g _ _ hf hg => exact W₂.add_mem hf hg
  | smul c f _ hf => exact W₂.smul_mem c hf

theorem main : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  intro E _ _ _ a b K₁ K₂ W₁ W₂ F hF
  obtain ⟨hl, hk⟩ := hF
  refine ⟨?_, ?_⟩
  · rintro φ m₂ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl u hu 1 K₂.one_mem (g, m₂)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_left W₁ W₂ _ (hk (g, m₂))
      simpa [hφ, Prod.mk_mul_mk] using this
  · rintro φ m₁ hφ
    refine ⟨?_, ?_⟩
    · intro u hu g
      have := hl 1 K₁.one_mem u hu (m₁, g)
      simpa [hφ, Prod.mk_mul_mk] using this
    · intro g
      have := restrict_right W₁ W₂ _ (hk (m₁, g))
      simpa [hφ, Prod.mk_mul_mk] using this

end GlobalTheory.CompanionTheory.EGlue.SliceTypePf

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_type : GlobalTheory.CompanionTheory.EGlue.SliceType := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.SliceTypePf.main
end

section
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embedding : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.PairEmb := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hull_generation : GlobalTheory.CompanionTheory.EGlue.HullGen := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.hullGen
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem adjoin_lie_equiv {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    {U : Submodule ℂ (Sm E N)} (T : Sm E N →ₗ[ℂ] Sm E N) (hU : IsStable U)
    (hT : ∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) {z : Module.End ℂ (Sm E N)}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range (lie E N))) :
    ∀ χ ∈ U, z χ ∈ U ∧ T (z χ) = z (T χ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact fun χ hχ => ⟨hU (.lie X) χ hχ, hT (.lie X) χ hχ⟩
  | algebraMap c =>
    intro χ hχ
    simpa [Module.algebraMap_end_apply] using U.smul_mem c hχ
  | add x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨x₁, x₂⟩ := hx χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    exact ⟨by simpa using U.add_mem x₁ y₁, by simp [x₂, y₂]⟩
  | mul x y _ _ hx hy =>
    intro χ hχ
    obtain ⟨y₁, y₂⟩ := hy χ hχ
    obtain ⟨x₁, x₂⟩ := hx _ y₁
    exact ⟨by simpa [Module.End.mul_apply] using x₁, by simp [Module.End.mul_apply, x₂, y₂]⟩

theorem capEquiv : CapEquiv := by
  intro E _ _ _ N U T ψ m hU hT hψ hc τ u
  rw [← (adjoin_lie_equiv T hU hT (GlobalTheory.CentreSmooth.cap_mem τ u) ψ hψ).2, hc τ u, map_smul]

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.capEquiv
end

section
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue

theorem discInf : DiscInf := by
  intro E _ _ _ M V hV τ
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := M) τ) (((M : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := GlobalTheory.DiscLocEx.exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩)
    (GlobalTheory.SpehInfChar.cap_commute_act τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.discInf
end

section
section
open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.Gl0.topInf
end

section
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.infOfEq_holds
end

section
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.EGlue

theorem convShift_holds : ConvShift := by
  intro E _ _ _ N t s z z₀ h hz
  induction h with
  | leaf V w w₀ hw => exact Conv.leaf V (fun k => w k + z k) (w₀ + z₀) (hw.add hz)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.convShift_holds
end

section
section
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem convComp_proved : ConvComp := by
  intro E _ _ _ N t s φ h hφ
  induction h with
  | leaf V z z₀ h => exact Conv.leaf V (fun k => z (φ k)) z₀ (h.comp hφ.tendsto_atTop)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_composition : GlobalTheory.CompanionTheory.EGlue.ConvComp := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.convComp_proved
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add, Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.ConvInf := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  intro h4 E _ _ _ N W hW
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
      ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
    intro U _ _ _ _ _ _ hU
    obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
      fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
    exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
  · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
    refine ⟨Ω, hΩ, fun K hK => ?_⟩
    obtain ⟨Θ, hΘ, h'⟩ := h K hK
    refine ⟨Θ, hΘ, ?_⟩
    intro U hs ha hg hn hc hi hU
    obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
    exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_induction : GlobalTheory.CompanionTheory.EGlue.FactorStep := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.factorStep_holds
end

section
section
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.MCl

theorem nodup_of_close {ε : ℝ} (hε : ε < 1 / 4) {m n : Multiset ℂ}
    (h : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n) (hg : GapM n) : m.Nodup := by
  induction h with
  | zero => exact Multiset.nodup_zero
  | @cons a b as bs hab hrel ih =>
    have hgn : (b ::ₘ bs).Nodup := hg.1
    have hb : b ∉ bs := (Multiset.nodup_cons.1 hgn).1
    have hg' : GapM bs := by
      refine ⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩
      exact hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy
    refine Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩
    obtain ⟨y, hy, hay⟩ := Multiset.exists_mem_of_rel_of_mem hrel ha
    have hne : b ≠ y := fun e => hb (e ▸ hy)
    have h1 := hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne
    have h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖ := by
      have : b - y = (a - y) - (a - b) := by ring
      rw [this]
      calc ‖(a - y) - (a - b)‖ ≤ ‖a - y‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - y‖ := add_comm _ _
    linarith

theorem prod_close (u : ℂ) (n : Multiset ℂ) : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : Multiset ℂ,
    Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n →
      ‖(m.map (u + ·)).prod - (n.map (u + ·)).prod‖ < δ := by
  induction n using Multiset.induction_on with
  | empty =>
    intro δ hδ
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have : m = 0 := Multiset.rel_zero_right.1 hm
    subst this
    simpa using hδ
  | cons b bs ih =>
    intro δ hδ
    have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod) :=
      continuous_mul.continuousAt
    obtain ⟨δ', hδ', H⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨ε₁, hε₁, H₁⟩ := ih δ' hδ'
    refine ⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩
    obtain ⟨a, as, hab, has, rfl⟩ := Multiset.rel_cons_right.1 hm
    have has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs :=
      has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)
    have h1 : ‖(u + a) - (u + b)‖ < δ' := by
      have e : (u + a) - (u + b) = a - b := by ring
      rw [e]
      have := hab.trans (min_le_right _ _)
      linarith
    have h2 := H₁ as has'
    have hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ' := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1, h2⟩
    have h3 := H hd
    rw [dist_eq_norm] at h3
    simpa [Multiset.map_cons, Multiset.prod_cons] using h3

end GlobalTheory.CompanionTheory.EGlue.MCl

namespace GlobalTheory.CompanionTheory.EGlue

theorem mCloseFacts_holds : MCloseFacts := by
  refine ⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg,
    fun m n hm u => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Multiset.exists_mem_of_rel_of_mem h hx
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    have h2 := hB y hy
    have h3 : ‖x - y‖ ≤ ε := hxy
    linarith
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, H⟩ := MCl.prod_close u n δ hδ
    filter_upwards [hm ε hε] with k hk
    rw [dist_eq_norm]
    exact H _ hk

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_facts_alt : GlobalTheory.CompanionTheory.EGlue.MCloseFacts := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds
end

section
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_limit : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound → GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts → GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.FactorLimProof.factorLim_of_parts
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := GlobalTheory.T.pair_slices
  have hP1 := GlobalTheory.T.pair_first_step hPS
  have hP2 := GlobalTheory.T.pair_second_step hPS
  have hCE := GlobalTheory.T.capacity_equivalence
  have hDI := GlobalTheory.T.discrete_infimum
  have hTI := GlobalTheory.T.topological_infimum
  have hIE := GlobalTheory.T.infimum_of_equality
  have hCS := GlobalTheory.T.convergence_strip
  have hCC := GlobalTheory.T.convergence_composition
  have hMC := GlobalTheory.T.closure_facts_alt
  eFinalGlue_of hCS hCC GlobalTheory.T.factor_induction (GlobalTheory.T.limit_lists hCS GlobalTheory.T.convergence_shift hCC)
    (GlobalTheory.T.single_gluing hPS GlobalTheory.T.pair_restriction GlobalTheory.T.pair_finite_dimensional GlobalTheory.T.slice_type hP1 hP2 GlobalTheory.T.hull_generation hCE)
    (GlobalTheory.T.factor_limit hCC (GlobalTheory.T.limit_trees hCC) (GlobalTheory.T.leaf_bound_alt hDI hTI hIE) (GlobalTheory.T.convergence_infimum hDI hTI) hIE hCE hMC)
    hMC (GlobalTheory.T.pair_embedding hPS hP1 hP2) hPS GlobalTheory.T.slice_type

end GlobalTheory.CompanionTheory.EGlue

end
end

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e45_final_gluing : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.eFinalGlue
end SpectralAccumulation
end BcB
end Rg
end PositivityTheory
end
