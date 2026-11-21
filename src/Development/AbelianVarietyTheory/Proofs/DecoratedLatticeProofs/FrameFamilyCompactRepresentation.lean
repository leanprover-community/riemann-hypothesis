import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory

theorem exists_finset_eval_injective {Z : Type} (T : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ T] :
    ∃ Y : Finset Z, ∀ g ∈ T, (∀ y ∈ Y, g y = 0) → g = 0 := by
  classical
  let φ : Z → Module.Dual ℂ T := fun z => (LinearMap.proj z).comp T.subtype
  have hfg : (Submodule.span ℂ (Set.range φ)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [← Set.image_univ] at hs'
  obtain ⟨Y, -, rfl⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨Y, fun g hg hY => ?_⟩
  have hle : Submodule.span ℂ (Set.range φ) ≤ LinearMap.ker (Module.Dual.eval ℂ T ⟨g, hg⟩) := by
    rw [hspan, Submodule.span_le]
    intro ψ hψ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    simp [φ, hY y hy]
  funext z
  have hz := hle (Submodule.subset_span ⟨z, rfl⟩)
  simpa [φ] using hz

theorem finiteDimensional_span_separately (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type)
    (S : ∀ i, Submodule ℂ (X i → ℂ)) (hS : ∀ i, FiniteDimensional ℂ (S i)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}) := by
  classical
  choose Y hY using fun i => @exists_finset_eval_injective (X i) (S i) (hS i)
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}
      add_mem' := fun {f g} hf hg i x => (S i).add_mem (hf i x) (hg i x)
      zero_mem' := fun i x => (S i).zero_mem
      smul_mem' := fun c f hf i x => (S i).smul_mem c (hf i x) }
  have hle : Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i} ≤ P :=
    Submodule.span_le.2 fun f hf => hf
  let L : P →ₗ[ℂ] ((∀ i, Y i) → ℂ) :=
    { toFun := fun f y => (f : (∀ i, X i) → ℂ) (fun i => (y i : X i))
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfP : ∀ i x, (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) ∈ S i := f.2
    have key : ∀ A : Finset ι, ∀ x : ∀ i, X i, (∀ j ∉ A, x j ∈ Y j) →
        (f : (∀ i, X i) → ℂ) x = 0 := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro x hx
        have h0 := congrFun hf (fun j => ⟨x j, hx j (by simp)⟩)
        simpa [L] using h0
      | @insert i A hiA ih =>
        intro x hx
        have hg : (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) = 0 := by
          refine hY i _ (hfP i x) ?_
          intro y hy
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst hji
            simpa using hy
          · rw [Function.update_of_ne hji]
            exact hx j (by simp [hji, hj])
        have h1 := congrFun hg (x i)
        simpa using h1
    apply Subtype.ext
    funext x
    exact key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)
  have : FiniteDimensional ℂ P := Module.Finite.of_injective L hL
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end

section
namespace GlobalTheory.CoefficientSpanFinite

theorem finiteDimensional_span_coefficients {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let Φ : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range Φ := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ∘ₗ LinearMap.applyₗ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CoefficientSpanFinite
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.SepTypes

theorem coeffSpan_finiteDimensional {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients
  | (apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFinite.finiteDimensional_span_coefficients ..)

theorem coeffSpan_rtrans {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) (c : G) {h : G → ℂ} (hh : h ∈ coeffSpan ρ) :
    (fun k => h (k * c)) ∈ coeffSpan ρ := by
  have hle : coeffSpan ρ ≤ (coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (fun k : G => k * c)) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ c w, funext fun k => ?_⟩
    simp [LinearMap.funLeft, map_mul]
  exact hle hh

theorem exists_space {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {Γ : ι → Type} [∀ i, Group (Γ i)] (K : Subgroup G) (j : (∀ i, Γ i) →* K)
    (hjs : Function.Surjective j) (a : ∀ i, Γ i → G) (hj : ∀ i k, (j (Pi.mulSingle i k) : G) = a i k)
    (W : ι → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : ∀ i, Representation ℂ (Γ i) (W i)) :
    ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧
      (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧
      ∀ φ : G → ℂ, Continuous φ → (∀ i x, (fun k => φ (x * a i k)) ∈ coeffSpan (ρ i)) →
        ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  let S : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ τ (k₀ : K), (fun κ => f (k₀ * j (Pi.mulSingle τ κ))) ∈ coeffSpan (ρ τ)}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun τ k₀ => Submodule.add_mem _ (ha.2 τ k₀) (hb.2 τ k₀)⟩
      zero_mem' := ⟨continuous_const, fun τ k₀ => Submodule.zero_mem _⟩
      smul_mem' := fun c {a} ha => ⟨ha.1.const_smul c, fun τ k₀ => Submodule.smul_mem _ c (ha.2 τ k₀)⟩ }
  have hfd : ∀ τ, FiniteDimensional ℂ (coeffSpan (ρ τ)) := fun τ => coeffSpan_finiteDimensional (ρ τ)
  have hfin := GlobalTheory.finiteDimensional_span_separately ι Γ (fun τ => coeffSpan (ρ τ)) hfd
  have hupd : ∀ (x : ∀ τ, Γ τ) τ y,
      Function.update x τ y = Function.update x τ 1 * Pi.mulSingle τ y := by
    intro x τ y
    funext τ'
    by_cases h : τ' = τ
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
  let M := Submodule.span ℂ {F : (∀ τ, Γ τ) → ℂ |
    ∀ τ x, (fun y => F (Function.update x τ y)) ∈ coeffSpan (ρ τ)}
  let T : S →ₗ[ℂ] M :=
    { toFun := fun f => ⟨fun x => (f : K → ℂ) (j x), Submodule.subset_span fun τ x => by
        have := f.2.2 τ (j (Function.update x τ 1))
        convert this using 2 with y
        rw [hupd x τ y, map_mul]⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hT : Function.Injective T := by
    intro a b hab
    have := congrArg (fun u : M => (u : (∀ τ, Γ τ) → ℂ)) hab
    apply Subtype.ext
    funext k
    obtain ⟨x, rfl⟩ := hjs k
    exact congrFun this x
  refine ⟨S, Module.Finite.of_injective T hT, fun f hf => hf.1, ?_, ?_⟩
  · intro f hf k
    refine ⟨hf.1.comp (continuous_id.mul continuous_const), fun τ k₀ => ?_⟩
    obtain ⟨κ₁, rfl⟩ := hjs k
    have key : ∀ κ, k₀ * j (Pi.mulSingle τ κ) * j κ₁ =
        (k₀ * j (Function.update κ₁ τ 1)) * j (Pi.mulSingle τ (κ * κ₁ τ)) := by
      intro κ
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul]
      congr 2
      funext τ'
      by_cases h : τ' = τ
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    simp only [key]
    exact coeffSpan_rtrans (ρ τ) (κ₁ τ) (hf.2 τ _)
  · intro φ hφ hty g
    refine ⟨hφ.comp (continuous_const.mul continuous_subtype_val), fun τ k₀ => ?_⟩
    have := hty τ (g * (k₀ : G))
    simpa only [Subgroup.coe_mul, hj, mul_assoc] using this

end GlobalTheory.SepTypes

theorem GlobalTheory.typesFiniteSpace : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D), ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ K : Subgroup (GA D V), (∃ j : (∀ τ, Formalism.REAL.KG (ε τ)) →* K, Function.Surjective j ∧ ∀ τ k, (j (Pi.mulSingle τ k) : GA D V) = kAt θ V τ (ε τ) (fr τ) k) → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), ∃ S : Submodule ℂ (K → ℂ), FiniteDimensional ℂ S ∧ (∀ f ∈ S, Continuous f) ∧ (∀ f ∈ S, ∀ k, (fun x => f (x * k)) ∈ S) ∧ ∀ φ : GA D V → ℂ, Continuous φ → (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) → ∀ g, (fun k : K => φ (g * k)) ∈ S := by
  intro D θ _ V ε fr _ K ⟨j, hjs, hj⟩ W _ _ _ ρ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  exact GlobalTheory.SepTypes.exists_space K j hjs (fun τ k => kAt θ V τ (ε τ) (fr τ) k) hj W ρ
end
