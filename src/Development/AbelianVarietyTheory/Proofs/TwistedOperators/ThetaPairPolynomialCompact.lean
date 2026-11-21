import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigenStatement
import BuildAid.ForwardExisting

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockVac

theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  by_cases h : ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧ g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h
    have hle : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {g} := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M B.ψ B.emb hP.base.cm hP.base.std
        (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) f g hg hg0 hf
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  · push_neg at h
    have hb : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} = ⊥ :=
      Submodule.span_eq_bot.2 fun f hf => by_contra fun h0 => h0 (h f hf)
    rw [hb]
    infer_instance

end GlobalTheory.FockVac
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  atlas_forward_decl GlobalTheory.FockVac.span_finiteDimensional
end

section
section
namespace GlobalTheory

open Submodule

theorem exists_finiteDimensional_orbit_of_generated :
    ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  intro V ι K _ _ U G P D m L T a hG hDL hGP hDP hmin hTG ha hTD f hf
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → Submodule ℂ V, Q 0 = span ℂ G ∧
      ∀ n, Q (n + 1) = Q n ⊔ span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) :=
    ⟨fun n => Nat.rec (span ℂ G) (fun _ R => R ⊔ span ℂ (⋃ u ∈ U, (D u) '' (R : Set V))) n,
      rfl, fun _ => rfl⟩
  have hmono : Monotone Q := monotone_nat_of_le_succ fun n => by
    rw [hQs]; exact le_sup_left
  have hDQ : ∀ n, ∀ u ∈ U, ∀ x ∈ Q n, D u x ∈ Q (n + 1) := by
    intro n u hu x hx
    rw [hQs]
    exact mem_sup_right (subset_span (Set.mem_iUnion₂.2 ⟨u, hu, x, hx, rfl⟩))
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (Q n) := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact hG
    | succ n ih =>
      rw [hQs]
      have hle : span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) ≤ ⨆ i, (Q n).map (L i) := by
        refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
        rintro _ ⟨x, hx, rfl⟩
        refine (span_le.2 ?_) (hDL u hu x)
        rintro _ ⟨i, rfl⟩
        exact mem_iSup_of_mem i (mem_map_of_mem hx)
      haveI : FiniteDimensional ℂ (span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))) :=
        Submodule.finiteDimensional_of_le hle
      exact Submodule.finiteDimensional_sup _ _
  have hQP : ∀ n, Q n ≤ P := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact span_le.2 hGP
    | succ n ih =>
      rw [hQs]
      refine sup_le ih (span_le.2 (Set.iUnion₂_subset fun u hu => ?_))
      rintro _ ⟨y, hy, rfl⟩
      exact hDP u hu y (ih hy)
  have hT : ∀ n k, Q n ≤ (Q n).comap (T k) := by
    intro n k
    induction n with
    | zero => rw [hQ0]; exact span_le.2 fun g hg => hTG k g hg
    | succ n ih =>
      rw [hQs]
      refine sup_le (ih.trans (comap_mono le_sup_left)) ?_
      refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
      rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ P := hQP n hx
      rw [SetLike.mem_coe, mem_comap, ← hQs, hTD k u hu x hxP]
      exact hDQ n (a k u) (ha k u hu) (T k x) (ih hx)
  have hGN : G ⊆ (⨆ n, Q n : Submodule ℂ V) := fun g hg =>
    mem_iSup_of_mem 0 (hQ0 ▸ subset_span hg)
  have hDN : ∀ u ∈ U, ∀ x ∈ (⨆ n, Q n : Submodule ℂ V), D u x ∈ (⨆ n, Q n : Submodule ℂ V) := by
    intro u hu x hx
    obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 hx
    exact mem_iSup_of_mem (n + 1) (hDQ n u hu x hn)
  obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 (hmin _ hGN hDN hf)
  exact ⟨Q n, hfin n, fun k => hT n k hn⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated : ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  atlas_forward_decl GlobalTheory.exists_finiteDimensional_orbit_of_generated
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockKFin

theorem kFinite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP f hf
  have hPA := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff hDspan using hD
  have hK := hPA.2.1
  simp only [GlobalTheory.RealActs.OpOn] at hK
  choose! Tk hTpres hTacts using hK
  have hGP : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → f₀ ∈ M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hmin : ∀ N : Submodule ℂ (SInf F (Fin n × Fin d)), {f₀ | M.IsGauss B.ψ B.emb f₀} ⊆ N →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | At (evI F) u}, ∀ g ∈ N, Dfun u g ∈ N) → M.Pol B.ψ B.emb ≤ N := by
    intro N hG hN
    refine sInf_le ⟨fun f₀ h => hG h, fun u hu g hg g₁ hg₁ => ?_⟩
    rw [(hDiff u hu g g₁).1 hg₁]
    exact hN u hu g hg
  have hAt : ∀ k : UA σ X.J, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k * u) :=
    fun k u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨S, hS, hSk⟩ := GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated (SInf F (Fin n × Fin d)) (Matrix (Fin n) (Fin d) (AE F E))
    {k // k ∈ KInf σ X B.emb} {u | At (evI F) u} {f₀ | M.IsGauss B.ψ B.emb f₀} (M.Pol B.ψ B.emb) Dfun m L
    (fun k => Tk k.1) (fun k u => mat k.1 * u) (GlobalTheory.T.fockVacua_span_finiteDimensional F E σ B n d X W M χX χW om r s r' s' hP)
    (fun u hu g => hDspan u hu g) (fun f₀ h => hGP f₀ h) (fun u hu g hg => hclos u hu g hg) hmin
    (fun k g hg => Submodule.subset_span
      (GlobalTheory.T.gaussian_compact_action_eigen hPr F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 g hg _
        ((hTacts k.1 k.2 g (hGP g hg) _).2 rfl)))
    (fun k u hu => hAt k.1 u hu)
    (fun k u hu g hg => (hDiff _ (hAt k.1 u hu) _ _).1
      (GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 u hu g (Dfun u g) (Tk k.1 g)
        (Tk k.1 (Dfun u g)) ((hDiff u hu g _).2 rfl) ((hTacts k.1 k.2 g hg _).2 rfl)
        ((hTacts k.1 k.2 _ (hclos u hu g hg) _).2 rfl)))
    f hf
  exact ⟨S, hS, fun k hk f₁ hact => by rw [(hTacts k hk f hf f₁).1 hact]; exact hSk ⟨k, hk⟩⟩

end GlobalTheory.FockKFin
end
