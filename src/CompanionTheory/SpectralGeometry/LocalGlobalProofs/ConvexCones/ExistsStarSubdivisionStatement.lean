import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StrictStarFunctionBoundsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut

section
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist

section Twist

variable {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O}

variable {X : Type} [AddCommGroup X] [Module O X]

theorem mem_balForms_twist (hb : CMOrd O bar) (τ : O ≃+* O) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (bar a) • z)
    rw [h2, hb.comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (bar (τ.symm a)) • z) at this
    rwa [hb.comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwG {φ : InvFun O} (hφ : IsTwG w0 φ) (τ : O ≃+* O) (hτ : τ w0 = w0)
    [Module.Finite O X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite O X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → O) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module O X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm

omit [Module O X] in

theorem depthSet_twist_subset (hb : CMOrd O bar) {ψ w : InvFun O} (hψ : IsTwG w0 ψ) (hw : IsTwG w0 w) (σ : O ≃+* O)
    (hσ : σ w0 = w0) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    depthSet bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ w0 = w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → O) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : O) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite O X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → O) →ₗ[O] X₁) hs
  have hd' := isStarDepth_transfer bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist hb τ)
    (eval_twist_of_isTwG hψ τ hτ hf') (eval_twist_of_isTwG hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

end Twist

theorem isTwG_starDepth : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ w : InvFun O), IsTwG w0 ψ → IsTwG w0 w → IsTwG w0 (starDepth bar ψ w) := by
  intro O _ _ _ _ bar w0 hb ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset hb hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset hb hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_depth_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ w : InvFun O), IsTwG w0 ψ → IsTwG w0 w → IsTwG w0 (starDepth bar ψ w) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_function_linear_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (K D : ℕ), IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | exact GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn <;> assumption)
end

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan GlobalTheory.PolFan.StarCells

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses

theorem isStarOf_of_clauses : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar _ q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩
  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone O bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_star_of_clauses : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf bar q ψ w ψ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses.isStarOf_of_clauses | exact GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses.isStarOf_of_clauses | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses.isStarOf_of_clauses <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover

private theorem inRCone_mono_of_range_subset {X : Type} [AddCommGroup X] {m n : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X)
    (hsub : Set.range γ' ⊆ Set.range γ) {β : LinearMap.BilinForm ℤ X}
    (h : GlobalTheory.PolFan.InRCone γ' β) : GlobalTheory.PolFan.InRCone γ β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  choose j hj using fun i => hsub (Set.mem_range_self i)
  refine ⟨fun a => ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i,
    fun a => Finset.sum_nonneg fun i _ => hc i, ?_⟩
  rw [hβ]
  symm
  calc ∑ a, (∑ i ∈ Finset.univ.filter (fun i => j i = a), c i) • GlobalTheory.PolFan.toReal (γ a)
      = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => j i = a), c i • GlobalTheory.PolFan.toReal (γ (j i)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ (j i)) := Finset.sum_fiberwise _ _ _
    _ = ∑ i, c i • GlobalTheory.PolFan.toReal (γ' i) := by simp_rw [hj]

theorem isStarOf_finite_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone bar X,
      ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hC hStar X _ _ _ _ hq
  classical
  obtain ⟨hS1, hS2, -⟩ := hStar
  obtain ⟨S0, hS0, hcov⟩ := (hψ X hq).finite
  obtain ⟨ch, hch⟩ : ∃ ch : Set (LinearMap.BilinForm ℤ X) → LinearMap.BilinForm ℤ X,
      ∀ T : Set (LinearMap.BilinForm ℤ X),
        (∃ β, β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β) →
        (ch T ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ ch T y y) ∧ w.evalZ (ch T) = 1 ∧
          ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
            Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ (ch T)) :=
    ⟨fun T => @Classical.epsilon _ ⟨0⟩ (fun β => β ∈ GlobalTheory.PolFan.balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧
        w.evalZ β = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), GlobalTheory.PolFan.IsCell bar ψ γ ∧
          Set.range γ = T ∧ GlobalTheory.PolFan.InRCone γ β),
      fun T h => Classical.epsilon_spec h⟩
  refine ⟨S0 ∪ ch '' {T | T ⊆ S0}, hS0.union (hS0.finite_subsets.image _), ?_⟩
  intro B hB
  obtain ⟨e, m, γ, c, hcell, hγS, hc, hBe⟩ := hcov B hB
  by_cases hz : ∀ β ∈ GlobalTheory.PolFan.balForms bar X, (∀ y, 0 ≤ β y y) → GlobalTheory.PolFan.InRCone γ β → w.evalZ β = 0
  · exact ⟨e, m, γ, c, hS1 X hq m γ hcell hz, fun i => Set.mem_union_left _ (hγS i), hc, hBe⟩
  · push Not at hz
    obtain ⟨β₀, hbal, hpsd, hin, hne⟩ := hz
    have hw1 : w.evalZ β₀ = 1 := ((hC X hq).1 β₀ hbal hpsd).resolve_left hne
    have hβne : β₀ ≠ 0 := by
      intro h0
      have h21 := (hC X hq).2.1 β₀ hbal hpsd hw1 2 0 (by rw [h0, smul_zero])
      omega
    have hsymm : ∀ (i : Fin m) (y z : X), (γ i) y z = (γ i) z y := fun i =>
      (show (∀ y z : X, (γ i) y z = (γ i) z y) ∧ _ from hcell.mem i).1
    have hBr : GlobalTheory.PolFan.pullR e.toLinearMap B ∈ GlobalTheory.PolCell.rcone γ := by
      simp only [GlobalTheory.PolCell.rcone, Set.mem_ofPred_eq]
      exact ⟨c, hc, hBe⟩
    obtain ⟨m', s, h, hcut, hpos, hB'⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m γ β₀ (GlobalTheory.PolFan.pullR e.toLinearMap B) hsymm hcell.nonneg hβne hin hBr
    obtain ⟨t, ht, htB⟩ := hB'
    refine ⟨e, m' + 1, Fin.cons β₀ fun j => γ (s j), t,
      hS2 X hq m γ hcell β₀ hbal hpsd hw1 hin m' s h hcut hpos, ?_, ht, htB⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
      refine Set.mem_union_right _ ⟨Set.range γ, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        exact hγS i
      · obtain ⟨hb', hp', hw', m'', γ'', hcell'', hrange, hin''⟩ :=
          hch (Set.range γ) ⟨β₀, hbal, hpsd, hw1, m, γ, hcell, rfl, hin⟩
        have hin2 : GlobalTheory.PolFan.InRCone γ (ch (Set.range γ)) :=
          inRCone_mono_of_range_subset γ γ'' hrange.le hin''
        exact (hC X hq).2.2 m γ hcell _ hb' hp' β₀ hbal hpsd hw' hw1 hin2 hin
    · rw [Fin.cons_succ]
      exact Set.mem_union_left _ (hγS (s j))

end GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan

theorem isPolyFan_star : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan bar q ψ' := by
  intro O _ _ _ _ bar hO q ψ w ψ' hψ hc hs hint hpos
  unfold GlobalTheory.PolFan.IsPolyFan
  intro X _ _ _ _ hX
  obtain ⟨S, hSf, hS⟩ := GlobalTheory.CompanionTheory.Ar.Fan.StarFiniteCover.isStarOf_finite_cover O bar hO q ψ w ψ' hψ hc hs X hX
  refine ⟨GlobalTheory.PolFan.StarFan.homog_of_cover O bar ψ' X ?_, GlobalTheory.T.superadditive_of_cells_cover_cone O bar ψ' X ?_, hint X hX, hpos X hX,
    ⟨S, hSf, hS⟩⟩
  all_goals
    intro B hB
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hS B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_integral_values_polyhedral : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w ψ' : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → IsStarOf bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan bar q ψ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan.isPolyFan_star | exact GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan.isPolyFan_star | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan.isPolyFan_star <;> assumption)
end

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision

theorem isTwG_starFun {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O} {ψ w : InvFun O}
    (hψ : IsTwG w0 ψ) (hd : IsTwG w0 (starDepth bar ψ w)) (K D : ℕ) :
    IsTwG w0 (starFun bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

theorem exists_starSubdivision : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 w → IsCentreSet bar q ψ w → ∃ ψ' : InvFun O, IsPolyFan bar q ψ' ∧ IsTwG w0 ψ' ∧ Subordinate bar q ψ' ψ ∧ IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar w0 hb q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := GlobalTheory.T.strict_star_function_bounds O bar hb q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.star_function_linear_on_cell O bar hb q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell bar (starFun bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell bar (starFun bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf bar q ψ w (starFun bar ψ w K D) := GlobalTheory.T.is_star_of_clauses O bar hb q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun bar ψ w K D, GlobalTheory.T.star_integral_values_polyhedral O bar hb q ψ w _ hψ hW hstar hint hpos,
    isTwG_starFun htψ (GlobalTheory.T.star_depth_twisted_galois O bar w0 hb ψ w htψ htw) K D, GlobalTheory.T.starSubdivision_subordinate_to_fan _ bar q ψ w _ hstar, hstar⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_star_subdivision : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 w → IsCentreSet bar q ψ w → ∃ ψ' : InvFun O, IsPolyFan bar q ψ' ∧ IsTwG w0 ψ' ∧ Subordinate bar q ψ' ψ ∧ IsStarOf bar q ψ w ψ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision | exact GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision <;> assumption)
end
