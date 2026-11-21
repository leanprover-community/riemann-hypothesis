import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTripleMatchingExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRepresentationTripleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]

theorem lsum_mapRange (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (b : κ → Pr →ₗ[ℂ] Pi) (hb : ∀ k i, b k ∘ₗ ρ i = σ i ∘ₗ b k) (i : ι) (d : κ →₀ Pr) :
    Finsupp.lsum ℂ b (Finsupp.mapRange (ρ i) (map_zero _) d) = σ i (Finsupp.lsum ℂ b d) := by
  have : (Finsupp.lsum ℂ b) ∘ₗ (Finsupp.mapRange.linearMap (ρ i)) = σ i ∘ₗ Finsupp.lsum ℂ b := by
    refine Finsupp.lhom_ext fun k x => ?_
    simp only [LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Finsupp.lsum_single]
    exact LinearMap.congr_fun (hb k i) x
  exact LinearMap.congr_fun this d

theorem eval_injective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (b : κ → Pr →ₗ[ℂ] Pi) (hli : LinearIndependent ℂ b) (hb : ∀ k i, b k ∘ₗ ρ i = σ i ∘ₗ b k) :
    ∀ c : κ →₀ Pr, Finsupp.lsum ℂ b c = 0 → c = 0 := by
  classical
  suffices h : ∀ n, ∀ c : κ →₀ Pr, c.support.card = n → Finsupp.lsum ℂ b c = 0 → c = 0 from
    fun c hc => h _ c rfl hc
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih c hcard hc
  by_contra hne
  obtain ⟨k₀, hk₀⟩ : ∃ k, k ∈ c.support := Finsupp.support_nonempty_iff.mpr hne
  set s := c.support with hs
  let R : Submodule ℂ (κ →₀ Pr) :=
    Finsupp.supported Pr ℂ (↑s : Set κ) ⊓ LinearMap.ker (Finsupp.lsum ℂ b)
  have memR : ∀ d, d ∈ R ↔ d.support ⊆ s ∧ Finsupp.lsum ℂ b d = 0 := by
    intro d; simp [R, Finsupp.mem_supported]
  have inj : ∀ d ∈ R, d k₀ = 0 → d = 0 := by
    intro d hd h0
    rw [memR] at hd
    have hsub : d.support ⊆ s.erase k₀ := by
      intro k hk
      refine Finset.mem_erase.mpr ⟨?_, hd.1 hk⟩
      rintro rfl; exact (Finsupp.mem_support_iff.mp hk) h0
    have hlt : d.support.card < n := by
      rw [← hcard]
      exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hk₀)
    exact ih _ hlt d rfl hd.2
  let π : R →ₗ[ℂ] Pr := (Finsupp.lapply k₀) ∘ₗ R.subtype
  have πinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    exact Subtype.ext (inj d.1 d.2 hd)
  have mapR : ∀ i, ∀ d ∈ R, Finsupp.mapRange (ρ i) (map_zero _) d ∈ R := by
    intro i d hd
    rw [memR] at hd ⊢
    refine ⟨fun k hk => hd.1 (Finsupp.support_mapRange hk), ?_⟩
    rw [lsum_mapRange ρ σ b hb, hd.2, map_zero]
  have hcR : c ∈ R := (memR c).mpr ⟨subset_refl _, hc⟩
  have hx0 : c k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀
  have πsurj : Function.Surjective π := by
    have hinv : ∀ i, ∀ x ∈ LinearMap.range π, ρ i x ∈ LinearMap.range π := by
      rintro i x ⟨d, rfl⟩
      exact ⟨⟨_, mapR i d.1 d.2⟩, by simp [π]⟩
    rcases hirr _ hinv with h | h
    · exfalso
      have : π ⟨c, hcR⟩ ∈ LinearMap.range π := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hx0 this
    · exact LinearMap.range_eq_top.mp h
  let E := LinearEquiv.ofBijective π ⟨πinj, πsurj⟩
  let T : κ → Module.End ℂ Pr := fun k => (Finsupp.lapply k) ∘ₗ R.subtype ∘ₗ E.symm.toLinearMap
  have hE : ∀ x, ((E.symm x : R) : κ →₀ Pr) k₀ = x := fun x => by
    have := E.apply_symm_apply x
    exact this
  have hT : ∀ k, ∀ i, T k * ρ i = ρ i * T k := by
    intro k i
    ext x
    have key : E.symm (ρ i x) = ⟨_, mapR i _ (E.symm x).2⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      change ρ i x = (Finsupp.mapRange (ρ i) (map_zero _) ((E.symm x : R) : κ →₀ Pr)) k₀
      rw [Finsupp.mapRange_apply, hE]
    simp [T, key]
  choose a ha using fun k => hschur (T k) (hT k)
  have ha0 : a k₀ = 1 := by
    have h1 : T k₀ (c k₀) = c k₀ := hE _
    rw [ha k₀] at h1
    have h2 : a k₀ • c k₀ = c k₀ := by simpa using h1
    have : (a k₀ - 1) • c k₀ = 0 := by rw [sub_smul, one_smul, h2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx0
  have hrel : ∑ k ∈ s, a k • b k = 0 := by
    ext x
    have hd := (memR _).mp (E.symm x).2
    have hsum := hd.2
    rw [Finsupp.lsum_apply, Finsupp.sum_of_support_subset _ hd.1 _ (fun k _ => map_zero _)] at hsum
    have hTx : ∀ k, ((E.symm x : R) : κ →₀ Pr) k = a k • x := fun k => by
      have := LinearMap.congr_fun (ha k) x
      simpa [T] using this
    simp only [hTx, map_smul] at hsum
    simpa [LinearMap.sum_apply] using hsum
  have := linearIndependent_iff'.mp hli s a hrel k₀ hk₀
  rw [ha0] at this
  exact one_ne_zero this

end GlobalTheory.ProductForm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]
variable {Q V : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup V] [Module ℂ V]

def factorSpace (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V) : Submodule ℂ (Pr →ₗ[ℂ] Pi) where
  carrier := {φ | ∃ f ∈ S, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q}
  zero_mem' := ⟨0, S.zero_mem, fun i => by simp, by simp⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hφ, hβ⟩ ⟨g, hg, hψ, hβ'⟩
    refine ⟨f + g, S.add_mem hf hg, fun i => ?_, ?_⟩
    · rw [LinearMap.add_comp, LinearMap.comp_add, hφ, hψ]
    · rw [map_add, hβ, hβ', LinearMap.add_comp]
  smul_mem' := by
    rintro a φ ⟨f, hf, hφ, hβ⟩
    refine ⟨a • f, S.smul_mem a hf, fun i => ?_, ?_⟩
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ]
    · rw [map_smul, hβ, LinearMap.smul_comp]

theorem mem_factorSpace {ρ : ι → Module.End ℂ Pr} {σ : ι → Module.End ℂ Pi} {q : Q →ₗ[ℂ] Pr}
    {β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi} {S : Submodule ℂ V} {φ : Pr →ₗ[ℂ] Pi} :
    φ ∈ factorSpace ρ σ q β S ↔ ∃ f ∈ S, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q := Iff.rfl

theorem comp_cancel {q : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) {φ ψ : Pr →ₗ[ℂ] Pi}
    (h : φ ∘ₗ q = ψ ∘ₗ q) : φ = ψ := by
  ext x
  obtain ⟨y, rfl⟩ := hq x
  exact LinearMap.congr_fun h y

def ev (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) : Pr ⊗[ℂ] F →ₗ[ℂ] Pi :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun x (φ : F) => (φ : Pr →ₗ[ℂ] Pi) x)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp))

@[simp] theorem ev_tmul (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (x : Pr) (φ : F) :
    ev F (x ⊗ₜ φ) = (φ : Pr →ₗ[ℂ] Pi) x := by
  simp [ev]

theorem ev_comp_symm (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) [DecidableEq κ] (b : Module.Basis κ ℂ F) :
    ev F ∘ₗ (TensorProduct.equivFinsuppOfBasisRight (M := Pr) b).symm.toLinearMap =
      Finsupp.lsum ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) := by
  refine Finsupp.lhom_ext fun k x => ?_
  simp [TensorProduct.equivFinsuppOfBasisRight_symm_apply]

theorem ev_surjective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V) (F : Submodule ℂ (Pr →ₗ[ℂ] Pi))
    (hF : factorSpace ρ σ q β S ≤ F)
    (hS : ∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q)
    (hspan : Submodule.span ℂ {y | ∃ f ∈ S, ∃ P, y = β f P} = ⊤) :
    Function.Surjective (ev F) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  rintro y ⟨f, hf, P, rfl⟩
  obtain ⟨φ, h1, h2⟩ := hS f hf
  refine ⟨q P ⊗ₜ ⟨φ, hF ⟨f, hf, h1, h2⟩⟩, ?_⟩
  rw [ev_tmul]
  exact (LinearMap.congr_fun h2 P).symm

theorem ev_injective (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (hF : ∀ φ ∈ F, ∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) :
    Function.Injective (ev F) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ F
  let E := TensorProduct.equivFinsuppOfBasisRight (M := Pr) b
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have hli : LinearIndependent ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) :=
    b.linearIndependent.map' F.subtype F.ker_subtype
  have h0 : Finsupp.lsum ℂ (fun k => ((b k : F) : Pr →ₗ[ℂ] Pi)) (E t) = 0 := by
    rw [← ev_comp_symm F b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]
  have := eval_injective ρ σ hirr hschur _ hli (fun k i => hF _ (b k).2 i) (E t) h0
  simpa using congrArg E.symm this

end GlobalTheory.ProductForm

namespace GlobalTheory.ProductForm

variable {ι Pr Pi κ : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi]
variable {Q V Q' V' : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup V'] [Module ℂ V']

theorem lsum_mapDomain_some (v : Option κ → Pr →ₗ[ℂ] Pi) (c : κ →₀ Pr) :
    Finsupp.lsum ℂ v (c.mapDomain some) = Finsupp.lsum ℂ (fun k => v (some k)) c := by
  have : Finsupp.lsum ℂ v ∘ₗ Finsupp.lmapDomain Pr ℂ some = Finsupp.lsum ℂ (fun k => v (some k)) :=
    Finsupp.lhom_ext fun k x => by simp
  exact LinearMap.congr_fun this c

theorem factorSpace_le (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi)
    (hirr : ∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hschur : ∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1)
    (q : Q →ₗ[ℂ] Pr) (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V)
    (q' : Q' →ₗ[ℂ] Pr) (β' : V' →ₗ[ℂ] Q' →ₗ[ℂ] Pi) (S' : Submodule ℂ V')
    (hS' : ∀ f ∈ S', ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β' f = φ ∘ₗ q')
    (hspan' : Submodule.span ℂ {y | ∃ f ∈ S', ∃ P, y = β' f P} = ⊤) :
    factorSpace ρ σ q β S ≤ factorSpace ρ σ q' β' S' := by
  classical
  intro φ hφ
  by_contra hφ'
  set F' := factorSpace ρ σ q' β' S'
  let b := Module.Basis.ofVectorSpace ℂ F'
  let b' : _ → Pr →ₗ[ℂ] Pi := fun k => ((b k : F') : Pr →ₗ[ℂ] Pi)
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ' (by rw [show φ = 0 from LinearMap.ext h]; exact F'.zero_mem)
  obtain ⟨t, ht⟩ := ev_surjective ρ σ q' β' S' F' le_rfl hS' hspan' (φ x)
  let E := TensorProduct.equivFinsuppOfBasisRight (M := Pr) b
  have hc' : Finsupp.lsum ℂ b' (E t) = φ x := by
    rw [← ev_comp_symm F' b, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply, ht]
  let v : Option _ → Pr →ₗ[ℂ] Pi := fun o => o.elim φ b'
  have hspanb : Submodule.span ℂ (Set.range b') = F' := by
    have : b' = F'.subtype ∘ b := rfl
    rw [this, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℂ v := by
    rw [linearIndependent_option]
    refine ⟨b.linearIndependent.map' F'.subtype F'.ker_subtype, ?_⟩
    change φ ∉ Submodule.span ℂ (Set.range b')
    rw [hspanb]
    exact hφ'
  have hv : ∀ o i, v o ∘ₗ ρ i = σ i ∘ₗ v o := by
    rintro (_ | k) i
    · obtain ⟨f, -, h1, -⟩ := hφ
      exact h1 i
    · obtain ⟨f, -, h1, -⟩ := (mem_factorSpace.mp (b k).2)
      exact h1 i
  have hrel : Finsupp.lsum ℂ v (Finsupp.single none x - (E t).mapDomain some) = 0 := by
    rw [map_sub, Finsupp.lsum_single, lsum_mapDomain_some]
    change φ x - Finsupp.lsum ℂ b' (E t) = 0
    rw [hc', sub_self]
  have h0 := congrArg (fun c : Option _ →₀ Pr => c none)
    (eval_injective ρ σ hirr hschur v hli hv _ hrel)
  simp only [Finsupp.coe_sub, _root_.Pi.sub_apply, Finsupp.single_eq_same, Finsupp.coe_zero,
    _root_.Pi.zero_apply] at h0
  rw [Finsupp.mapDomain_notin_range _ _ (by simp), sub_zero] at h0
  exact hx (by rw [h0, map_zero])

theorem exists_lift (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr)
    (hq : Function.Surjective q) (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (S : Submodule ℂ V)
    (F : Submodule ℂ (Pr →ₗ[ℂ] Pi)) (hF : factorSpace ρ σ q β S ≤ F)
    (hS : ∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q) :
    ∃ r : V →ₗ[ℂ] F, ∀ f ∈ S, ((r f : F) : Pr →ₗ[ℂ] Pi) ∘ₗ q = β f := by
  classical
  have hmem : ∀ f : S, ∃ φ ∈ factorSpace ρ σ q β S, β f = φ ∘ₗ q := fun f =>
    let ⟨φ, h1, h2⟩ := hS f f.2
    ⟨φ, ⟨f, f.2, h1, h2⟩, h2⟩
  choose g hg hgβ using hmem
  let r₀ : S →ₗ[ℂ] F :=
    { toFun := fun f => ⟨g f, hF (hg f)⟩
      map_add' := fun f f' => by
        ext1
        change g (f + f') = g f + g f'
        apply comp_cancel hq
        rw [LinearMap.add_comp, ← hgβ, ← hgβ, ← hgβ, Submodule.coe_add, map_add]
      map_smul' := fun a f => by
        ext1
        change g (a • f) = a • g f
        apply comp_cancel hq
        rw [LinearMap.smul_comp, ← hgβ, ← hgβ, Submodule.coe_smul, map_smul] }
  obtain ⟨r, hr⟩ := LinearMap.exists_extend r₀
  refine ⟨r, fun f hf => ?_⟩
  have : r f = r₀ ⟨f, hf⟩ := LinearMap.congr_fun hr ⟨f, hf⟩
  rw [this]
  exact (hgβ ⟨f, hf⟩).symm

end GlobalTheory.ProductForm

theorem GlobalTheory.SquareLM.productForm : ∀ (ι Pr Pi Q Q' V V' : Type) [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pi] [Module ℂ Pi] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  (ρ : ι → Module.End ℂ Pr) (σ : ι → Module.End ℂ Pi) (q : Q →ₗ[ℂ] Pr) (q' : Q' →ₗ[ℂ] Pr)
  (β : V →ₗ[ℂ] Q →ₗ[ℂ] Pi) (β' : V' →ₗ[ℂ] Q' →ₗ[ℂ] Pi) (S : Submodule ℂ V) (S' : Submodule ℂ V'),
  Function.Surjective q → Function.Surjective q' →
  (∀ N : Submodule ℂ Pr, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
  (∀ T : Module.End ℂ Pr, (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1) →
  (∀ f ∈ S, ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β f = φ ∘ₗ q) →
  (∀ f ∈ S', ∃ φ : Pr →ₗ[ℂ] Pi, (∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ) ∧ β' f = φ ∘ₗ q') →
  Submodule.span ℂ {y | ∃ f ∈ S, ∃ P, y = β f P} = ⊤ → Submodule.span ℂ {y | ∃ f ∈ S', ∃ P, y = β' f P} = ⊤ →
  ∃ (Pf : ModuleCat.{0} ℂ) (r : V →ₗ[ℂ] Pf) (r' : V' →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
    (∀ x, ∃ f ∈ S, r f = x) ∧ (∀ x, ∃ f ∈ S', r' f = x) ∧
    (∀ f ∈ S, ∀ P, β f P = e (q P ⊗ₜ r f)) ∧ ∀ f ∈ S', ∀ P, β' f P = e (q' P ⊗ₜ r' f) := by
  intro ι Pr Pi Q Q' V V' _ _ _ _ _ _ _ _ _ _ _ _ ρ σ q q' β β' S S' hq hq' hirr hschur hS hS'
    hspan hspan'
  classical
  let F := GlobalTheory.ProductForm.factorSpace ρ σ q β S
  have hle : GlobalTheory.ProductForm.factorSpace ρ σ q' β' S' ≤ F :=
    GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q' β' S' q β S hS hspan
  have hge : F ≤ GlobalTheory.ProductForm.factorSpace ρ σ q' β' S' :=
    GlobalTheory.ProductForm.factorSpace_le ρ σ hirr hschur q β S q' β' S' hS' hspan'
  have hFeq : ∀ φ ∈ F, ∀ i, φ ∘ₗ ρ i = σ i ∘ₗ φ := fun φ hφ i => by
    obtain ⟨f, -, h1, -⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp hφ
    exact h1 i
  obtain ⟨r, hr⟩ := GlobalTheory.ProductForm.exists_lift ρ σ q hq β S F le_rfl hS
  obtain ⟨r', hr'⟩ := GlobalTheory.ProductForm.exists_lift ρ σ q' hq' β' S' F hle hS'
  let e : Pr ⊗[ℂ] F ≃ₗ[ℂ] Pi := LinearEquiv.ofBijective (GlobalTheory.ProductForm.ev F)
    ⟨GlobalTheory.ProductForm.ev_injective ρ σ hirr hschur F hFeq,
      GlobalTheory.ProductForm.ev_surjective ρ σ q β S F le_rfl hS hspan⟩
  refine ⟨ModuleCat.of ℂ F, r, r', e, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨f, hf, -, hβ⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp (x : F).2
    exact ⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq ((hr f hf).trans hβ))⟩
  · intro x
    obtain ⟨f, hf, -, hβ⟩ := GlobalTheory.ProductForm.mem_factorSpace.mp (hge (x : F).2)
    exact ⟨f, hf, Subtype.ext (GlobalTheory.ProductForm.comp_cancel hq' ((hr' f hf).trans hβ))⟩
  · intro f hf P
    change β f P = GlobalTheory.ProductForm.ev F (q P ⊗ₜ r f)
    rw [GlobalTheory.ProductForm.ev_tmul, ← hr f hf]
    rfl
  · intro f hf P
    change β' f P = GlobalTheory.ProductForm.ev F (q' P ⊗ₜ r' f)
    rw [GlobalTheory.ProductForm.ev_tmul, ← hr' f hf]
    rfl
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareLM

theorem localMatching : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  intro hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, ρ, q, q', hq, hq', hrk, hirr, hfac⟩ := GlobalTheory.T.polynomial_representation_triple hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  let ι := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}
  have hirr' : ∀ N : Submodule ℂ Pr, (∀ i : ι, ∀ x ∈ N, ρ i.1.1 i.1.2 x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hirr N fun τ Y hY x hx => hN ⟨(τ, Y), hY⟩ x hx
  have hS := GlobalTheory.dixmier_commutant_scalar ι Pr (fun i => ρ i.1.1 i.1.2) hrk hirr'
  obtain ⟨h0, hadd, hsmul, hfadd, hfsmul⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ true W X A B
  obtain ⟨h0', hadd', hsmul', hfadd', hfsmul'⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ false W₁ X A₁ B
  refine ⟨Pr, q, q', hq, hq', fun α β htr hexp => ⟨GlobalTheory.T.weil_triple_matching_exists hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B α β htr, ?_⟩⟩
  intro ωA ωB Pi rf rl p p' hm
  obtain ⟨hfa, hfb⟩ := hfac α β htr hexp ωA ωB Pi rf rl p p' hm
  let S : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {f | IsFinF ψ θ true A B f}, add_mem' := fun hf hg => hadd _ _ hf hg, zero_mem' := h0,
      smul_mem' := fun c _ hf => hsmul c _ hf }
  let S' : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {f | IsFinF ψ θ false A₁ B f}, add_mem' := fun hf hg => hadd' _ _ hf hg, zero_mem' := h0',
      smul_mem' := fun c _ hf => hsmul' c _ hf }
  let βA : S →ₗ[ℂ] PolF D X.rank W.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p (fockF ψ θ true A B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  let βB : S' →ₗ[ℂ] PolF D X.rank W₁.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p' (fockF ψ θ false A₁ B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd' _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul' _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} {P : Type} [AddCommGroup P] [Module ℂ P] (pp : (WO M X → ℂ) →ₗ[ℂ] P),
      (algF ψ θ ε A' B).map pp = ⊤ →
      Submodule.span ℂ {y | ∃ f : {f // IsFinF ψ θ ε A' B f}, ∃ Q, y = pp (fockF ψ θ ε A' B f.1 Q)} = ⊤ := by
    intro M ε A' P _ _ pp h
    rw [← h, algF, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨f, Q, rfl⟩; exact ⟨_, ⟨f.1, Q, f.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, Q, hf, rfl⟩, rfl⟩; exact ⟨⟨f, hf⟩, Q, rfl⟩
  obtain ⟨Pf, r, r', e, hr, hr', he, he'⟩ := GlobalTheory.SquareLM.productForm ι Pr Pi _ _ _ _ (fun i => ρ i.1.1 i.1.2) (fun i => rl i.1.1 i.1.2)
    q q' βA βB ⊤ ⊤ hq hq' hirr' hS
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfa f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfb f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (by
      rw [← hspan p hm.mapA.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
    (by
      rw [← hspan p' hm.mapB.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
  obtain ⟨r₀, hr₀⟩ := LinearMap.exists_extend r
  obtain ⟨r₀', hr₀'⟩ := LinearMap.exists_extend r'
  have e₁ : ∀ f (hf : IsFinF ψ θ true A B f), r₀ f = r ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀ ⟨f, hf⟩
  have e₂ : ∀ f (hf : IsFinF ψ θ false A₁ B f), r₀' f = r' ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀' ⟨f, hf⟩
  refine ⟨Pf, r₀, r₀', e, fun x => ?_, fun x => ?_, fun f hf P => ?_, fun f hf P => ?_⟩
  · obtain ⟨f, _, h⟩ := hr x; exact ⟨f.1, f.2, by rw [e₁ f.1 f.2]; exact h⟩
  · obtain ⟨f, _, h⟩ := hr' x; exact ⟨f.1, f.2, by rw [e₂ f.1 f.2]; exact h⟩
  · rw [e₁ f hf]; exact he ⟨f, hf⟩ trivial P
  · rw [e₂ f hf]; exact he' ⟨f, hf⟩ trivial P

end GlobalTheory.SquareLM

end
end
