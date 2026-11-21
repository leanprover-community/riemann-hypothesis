import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PTypes
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TrStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem typeB_of_mem_typSp {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {U : Submodule ℂ (Sm E N)} {φ : Sm E N} (h : φ ∈ TypSp K W U) : TypeB K W φ := by
  induction h using Submodule.span_induction with
  | mem _ hx => exact hx.2
  | zero =>
    refine ⟨fun u _ g => rfl, fun g => ?_⟩
    have e : (fun k : Kinf E N => (0 : Sm E N).1 (g * infGL E N (Unitary.toUnits k))) = 0 := rfl
    rw [e]
    exact W.zero_mem
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
      rw [hx.1 u hu g, hy.1 u hu g]
    · have e : (fun k : Kinf E N => (x + y).1 (g * infGL E N (Unitary.toUnits k))) =
          (fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k))) +
            fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.add_mem (hx.2 g) (hy.2 g)
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show c * x.1 (g * finGL E N u) = c * x.1 g
      rw [hx.1 u hu g]
    · have e : (fun k : Kinf E N => (c • x).1 (g * infGL E N (Unitary.toUnits k))) =
          c • fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.smul_mem c (hx.2 g)

theorem typSp_le {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (U : Submodule ℂ (Sm E N)) : TypSp K W U ≤ U :=
  Submodule.span_le.2 fun _ h => h.1


theorem tensor_span_mono {a b : ℕ} {U₁ U₁' : Submodule ℂ (Sm E a)} {U₂ U₂' : Submodule ℂ (Sm E b)} (h₁ : U₁ ≤ U₁')
    (h₂ : U₂ ≤ U₂') : tens2 U₁ U₂ ≤ tens2 U₁' U₂' :=
  Submodule.span_mono fun _ ⟨φ₁, hφ₁, φ₂, hφ₂, e⟩ => ⟨φ₁, h₁ hφ₁, φ₂, h₂ hφ₂, e⟩

def prodBil {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (GA E a × GA E b → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ₁ φ₂ m => φ₁.1.1 m.1 * φ₂.1.1 m.2)
    (fun x y z => by funext m; simp [add_mul])
    (fun c x z => by funext m; simp [mul_assoc])
    (fun x y z => by funext m; simp [mul_add])
    (fun c x z => by funext m; simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]; ring)

theorem fd_tens2 {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) [FiniteDimensional ℂ U₁]
    [FiniteDimensional ℂ U₂] : FiniteDimensional ℂ (tens2 U₁ U₂) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift (prodBil U₁ U₂)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact ⟨(⟨φ₁, h₁⟩ : U₁) ⊗ₜ[ℂ] (⟨φ₂, h₂⟩ : U₂), by rw [TensorProduct.lift.tmul]; rfl⟩

theorem sep_left {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (X → ℂ)) (hj : Function.Injective j)
    (A : Submodule ℂ V) {n : ℕ} (f : Fin n → V) (g : Fin n → Y → ℂ)
    (hs : ∀ y, ∃ χ ∈ A, j χ = fun x => ∑ i, j (f i) x * g i y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ A) ∧ ∀ x y, ∑ i, j (f i) x * g i y = ∑ i, j (f' i) x * g i y := by
  have hinj : LinearMap.ker (j.comp A.subtype) = ⊥ :=
    LinearMap.ker_eq_bot.2 (hj.comp Subtype.val_injective)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (j.comp A.subtype) hinj
  refine ⟨fun i => (L (j (f i)) : V), fun i => (L (j (f i))).2, fun x y => ?_⟩
  obtain ⟨χ, hχ, e⟩ := hs y
  have e1 : (fun x => ∑ i, j (f i) x * g i y) = ∑ i, g i y • j (f i) := by
    funext x
    simp [Finset.sum_apply, mul_comm]
  have e2 : (⟨χ, hχ⟩ : A) = ∑ i, g i y • L (j (f i)) := by
    have h3 : L ((j.comp A.subtype) ⟨χ, hχ⟩) = ⟨χ, hχ⟩ := LinearMap.congr_fun hL _
    rw [← h3, LinearMap.comp_apply, Submodule.subtype_apply, e, e1, map_sum]
    simp only [map_smul]
  have e3 := congrArg (fun v : A => j (v : V) x) e2
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at e3
  rw [← congrFun e x, e3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sep_right {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Y → ℂ)) (hj : Function.Injective j)
    (B : Submodule ℂ V) {n : ℕ} (g : Fin n → X → ℂ) (f : Fin n → V)
    (hs : ∀ x, ∃ χ ∈ B, j χ = fun y => ∑ i, g i x * j (f i) y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ B) ∧ ∀ x y, ∑ i, g i x * j (f i) y = ∑ i, g i x * j (f' i) y := by
  obtain ⟨f', hf', e⟩ := sep_left (X := Y) (Y := X) j hj B f g fun x => by
    obtain ⟨χ, hχ, e⟩ := hs x
    exact ⟨χ, hχ, by rw [e]; funext y; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
  refine ⟨f', hf', fun x y => ?_⟩
  have := e y x
  calc ∑ i, g i x * j (f i) y = ∑ i, j (f i) y * g i x := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ∑ i, j (f' i) y * g i x := this
    _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem tens_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : GA E a × GA E b → ℂ} (hF : F ∈ tens2 U₁ U₂)
    (h₁ : ∀ y, TypF K₁ W₁ fun x => F (x, y)) (h₂ : ∀ x, TypF K₂ W₂ fun y => F (x, y)) :
    F ∈ tens2 (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  obtain ⟨n, ψ₁, ψ₂, hψ₁, hψ₂, rfl⟩ := InducedTensorMap.tensor_pair_finite_sum hF
  obtain ⟨φ₁, hφ₁, e₁⟩ := sep_left (Sm E a).subtype Subtype.val_injective (TypSp K₁ W₁ U₁) ψ₁
    (fun i y => (ψ₂ i).1 y) fun y => by
      refine ⟨∑ i, (ψ₂ i).1 y • ψ₁ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₁.smul_mem _ (hψ₁ i), ?_⟩, ?_⟩
      · have e : (∑ i, (ψ₂ i).1 y • ψ₁ i).1 = fun x => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext x
          simp [Finset.sum_apply, mul_comm]
        rw [typeB_iff, e]
        exact h₁ y
      · funext x
        simp [Finset.sum_apply, mul_comm]
  obtain ⟨φ₂, hφ₂, e₂⟩ := sep_right (Sm E b).subtype Subtype.val_injective (TypSp K₂ W₂ U₂)
    (fun i x => (φ₁ i).1 x) ψ₂ fun x => by
      refine ⟨∑ i, (φ₁ i).1 x • ψ₂ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₂.smul_mem _ (hψ₂ i), ?_⟩, ?_⟩
      · have e : (∑ i, (φ₁ i).1 x • ψ₂ i).1 = fun y => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext y
          have h := e₁ x y
          simp only [Submodule.subtype_apply] at h
          rw [h]
          simp [Finset.sum_apply]
        rw [typeB_iff, e]
        exact h₂ x
      · funext y
        simp [Finset.sum_apply]
  have e : (fun m : GA E a × GA E b => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      fun m => ∑ i, (φ₁ i).1 m.1 * (φ₂ i).1 m.2 := by
    funext m
    exact (e₁ m.1 m.2).trans (e₂ m.1 m.2)
  rw [e]
  exact InducedTensorMap.A.sum_mem hφ₁ hφ₂

theorem pair_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    F ∈ pairSpace (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  rw [tensor_span_eq_pair_space] at hF ⊢
  refine tens_typ hF (fun y => ⟨fun u hu g => ?_, fun g => ?_⟩) (fun x => ⟨fun u hu g => ?_, fun g => ?_⟩)
  · have := hT.1 u hu 1 (one_mem _) (g, y)
    simpa [map_one] using this
  · let R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun z k => z (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤
        W₁ := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [R, mul_comm]
      rw [e]
      exact W₁.smul_mem _ hw₁
    have hm := hR (Submodule.mem_map_of_mem (f := R) (hT.2 (g, y)))
    have e : R (fun k : Kinf E a × Kinf E b => F ((g, y) * (infGL E a (Unitary.toUnits k.1),
        infGL E b (Unitary.toUnits k.2)))) = fun k => F (g * infGL E a (Unitary.toUnits k), y) := by
      funext k
      simp [R, map_one]
    rw [e] at hm
    exact hm
  · have := hT.1 1 (one_mem _) u hu (x, g)
    simpa [map_one] using this
  · let R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun z k => z (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤
        W₂ := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [R]
      rw [e]
      exact W₂.smul_mem _ hw₂
    have hm := hR (Submodule.mem_map_of_mem (f := R) (hT.2 (x, g)))
    have e : R (fun k : Kinf E a × Kinf E b => F ((x, g) * (infGL E a (Unitary.toUnits k.1),
        infGL E b (Unitary.toUnits k.2)))) = fun k => F (x, g * infGL E b (Unitary.toUnits k)) := by
      funext k
      simp [R, map_one]
    rw [e] at hm
    exact hm

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.KTypeSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_sep {α : Type} (X : Submodule ℂ (α → ℂ)) [FiniteDimensional ℂ X] :
    ∃ S : Finset α, ∀ w ∈ X, (∀ a ∈ S, w a = 0) → w = 0 := by
  classical
  let Ker : Finset α → Submodule ℂ (α → ℂ) := fun S =>
    X ⊓ ⨅ a ∈ S, LinearMap.ker (LinearMap.proj a : (α → ℂ) →ₗ[ℂ] ℂ)
  have hmem : ∀ S w, w ∈ Ker S ↔ w ∈ X ∧ ∀ a ∈ S, w a = 0 := by
    intro S w
    simp only [Ker, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  have hfd : ∀ S, FiniteDimensional ℂ (Ker S) := fun S => Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ d, ∃ S, Module.finrank ℂ (Ker S) = d := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS0⟩ := Nat.find_spec hex
  have hS : ∀ S', Module.finrank ℂ (Ker S) ≤ Module.finrank ℂ (Ker S') := fun S' => by
    rw [hS0]
    exact Nat.find_min' hex ⟨S', rfl⟩
  refine ⟨S, fun w hw h0 => ?_⟩
  by_contra hne
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
  have hlt : Ker (insert a S) < Ker S := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun he => ?_)
    · rw [hmem] at hv ⊢
      exact ⟨hv.1, fun b hb => hv.2 b (Finset.mem_insert_of_mem hb)⟩
    · have hwS : w ∈ Ker S := (hmem S w).2 ⟨hw, h0⟩
      rw [← he, hmem] at hwS
      exact ha (hwS.2 a (Finset.mem_insert_self a S))
  have := hfd S
  exact absurd (hS (insert a S)) (not_le.2 (Submodule.finrank_lt_finrank_of_lt hlt))

theorem typSp_tw_le {n : ℕ} {K' : Subgroup (GL (Fin n) (Af E))} (hK : K' ≤ detKer n)
    (W' : Submodule ℂ (Kinf E n → ℂ)) (U : Submodule ℂ (Sm E n)) (z : ℂ) :
    TypSp K' W' (tw U z) ≤ (TypSp K' W' U).map (mulChi n (Model.absC E z)).toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨hφ, hT⟩
  obtain ⟨χ, hχ, rfl⟩ := hφ
  refine ⟨χ, Submodule.subset_span ⟨hχ, ?_⟩, rfl⟩
  have e : χ = mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) χ) :=
    (ParabolicProjection.mulChi_absC_neg n z χ).symm
  rw [e]
  exact t_typeB_mulChi hT hK (-z)

theorem finiteDimensional_type_space_of_disc (hA : AdmDisc) {N : ℕ} (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [hW : FiniteDimensional ℂ W] :
    ∀ {n : ℕ} (t : Tr E n), n ≤ N → t.Disc → FiniteDimensional ℂ (TypSp (Kf N K n) (Wf N W n) t.space) := by
  intro n t
  induction t with
  | leaf V z =>
    intro _ ht
    show FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) (tw V z))
    rcases ht with ⟨rfl, -, -⟩ | ⟨-, hV⟩
    · have : Subsingleton (GA E 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩
      infer_instance
    · have : FiniteDimensional ℂ (TypSp (Kf N K _) (Wf N W _) V) :=
        hA E _ _ _ (isOpen_Kf hK _) (fd_Wf hW _) V hV
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) (Wf N W _) V z)
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro hN ht
    obtain ⟨ht₁, ht₂⟩ := ht
    have : FiniteDimensional ℂ (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2))) := by
      have := ih₁ (by omega) ht₁
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    have : FiniteDimensional ℂ (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) := by
      have := ih₂ (by omega) ht₂
      exact Submodule.finiteDimensional_of_le (typSp_tw_le (Kf_le_det _) _ _ _)
    set Y := tens2 (TypSp (Kf N K r) (Wf N W r) (tw t₁.space ((s : ℂ) / 2)))
      (TypSp (Kf N K s) (Wf N W s) (tw t₂.space (-(r : ℂ) / 2))) with hY
    have : FiniteDimensional ℂ Y := fd_tens2 _ _
    set X := TypSp (Kf N K (r + s)) (Wf N W (r + s)) (Tr.node t₁ t₂).space with hX
    have : FiniteDimensional ℂ (Wf N W (r + s)) := fd_Wf hW _
    obtain ⟨S, hS⟩ := exists_sep (Wf N W (r + s))
    set T := Tset r s (Kf N K (r + s)) with hTdef
    have hI : ∀ φ ∈ X, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ := by
      intro φ hφ
      have hf : φ ∈ (Tr.node t₁ t₂).space := typSp_le _ _ _ hφ
      rw [Tr.space] at hf
      exact memInd2_of_span (Submodule.span_mono (fun φ h => h.1) hf)
    have key : ∀ φ ∈ X, ∀ t ∈ T, ∀ k : Kinf E (r + s),
        (fun m : GA E r × GA E s =>
          φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t))) ∈ Y := by
      intro φ hφ t ht k
      have hT := typeB_of_mem_typSp hφ
      refine tens_typ ((hI φ hφ).2 k t) (fun y => ⟨fun u hu x₁ => ?_, fun x₁ => ?_⟩)
        (fun x => ⟨fun u hu x₂ => ?_, fun x₂ => ?_⟩)
      · have h1 : lev (Ad E) r s (x₁ * finGL E r u, y) =
            lev (Ad E) r s (x₁, y) * finGL E (r + s) (lev (Af E) r s (u, 1)) := by
          rw [← Slice1.lev_finGL, map_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (u, 1))
        have e : lev (Ad E) r s (x₁ * finGL E r u, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x₁, y) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (u, 1) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (u, 1))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_left hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x₁, y) * finGL E (r + s) t)
        have hW₁ := Wf_left (W := W) hN hw k
        convert hW₁ using 1
        funext k₁
        show φ.1 _ = _
        rw [infGL_comm, ← mul_assoc, Slice1.lev_infGL_right]
        simp only [map_mul, Slice1.toUnits_levK]
      · have h1 : lev (Ad E) r s (x, x₂ * finGL E s u) =
            lev (Ad E) r s (x, x₂) * finGL E (r + s) (lev (Af E) r s (1, u)) := by
          rw [← Slice2.lev_finGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        have hc := infGL_comm (Unitary.toUnits k) (lev (Af E) r s (1, u))
        have e : lev (Ad E) r s (x, x₂ * finGL E s u) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) =
            lev (Ad E) r s (x, x₂) * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t) *
              finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
          rw [h1, map_mul, map_mul, map_inv]
          simp only [mul_assoc]
          rw [← mul_assoc (finGL E (r + s) (lev (Af E) r s (1, u))), ← hc]
          group
        show φ.1 _ = φ.1 _
        rw [e, hT.1 _ (Kf_right hN ht hu)]
      · have hw := typeB_lt hT (lev (Ad E) r s (x, x₂) * finGL E (r + s) t)
        have hW₂ := Wf_right (W := W) hN hw k
        convert hW₂ using 1
        funext k₂
        show φ.1 _ = _
        have h1 : lev (Ad E) r s (x, x₂ * infGL E s (Unitary.toUnits k₂)) =
            lev (Ad E) r s (x, x₂) * infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂)) := by
          rw [← Slice2.lev_infGL_one, ← map_mul, Prod.mk_mul_mk, mul_one]
        rw [h1]
        simp only [map_mul, Slice2.toUnits_levK]
        rw [infGL_comm (Unitary.toUnits k) t]
        simp only [← mul_assoc]
        rw [mul_assoc (lev (Ad E) r s (x, x₂)) (infGL E (r + s) (lev (Cinf E) r s (1, Unitary.toUnits k₂))),
          infGL_comm (lev (Cinf E) r s (1, Unitary.toUnits k₂)) t, ← mul_assoc]
    have inj : ∀ φ ∈ X, (∀ t ∈ T, ∀ k ∈ S, ∀ m : GA E r × GA E s,
        φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) t)) = 0) → φ = 0 := by
      intro φ hφ h0
      have hT := typeB_of_mem_typSp hφ
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨x, m, t, k, l, ht, hl, hg⟩ := Tset_spec (isOpen_Kf hK (r + s)) g
      have hw := hT.2 (lev (Ad E) r s m * finGL E (r + s) t)
      have hz := hS _ hw (fun κ hκ => by
        show φ.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0
        rw [mul_assoc, ← infGL_comm]
        exact h0 t ht κ hκ m)
      have e : g = unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) *
          finGL E (r + s) l := by
        rw [hg]
        simp only [mul_assoc]
      show φ.1 g = 0
      rw [e, hT.1 l hl, (hI φ hφ).1]
      exact congrFun hz k
    let f : X →ₗ[ℂ] (↥T × ↥S → Y) :=
      { toFun := fun φ p => ⟨fun m => φ.1.1 (lev (Ad E) r s m *
            (infGL E (r + s) (Unitary.toUnits p.2.1) * finGL E (r + s) p.1.1)),
          key φ.1 φ.2 p.1.1 p.1.2 p.2.1⟩
        map_add' := fun φ ψ => funext fun p => Subtype.ext (funext fun m => rfl)
        map_smul' := fun c φ => funext fun p => Subtype.ext (funext fun m => rfl) }
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    have h0 := inj φ.1 φ.2 fun t ht k hk m => by
      have := congrArg (fun F => (F (⟨t, ht⟩, ⟨k, hk⟩)).1 m) hφ
      exact this
    exact Subtype.ext h0

theorem fd_typSp (hA : AdmDisc) {N : ℕ} (t : Tr E N) (ht : t.Disc) (K : Subgroup (GL (Fin N) (Af E)))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (W : Submodule ℂ (Kinf E N → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (TypSp K W t.space) := by
  have := finiteDimensional_type_space_of_disc hA K hK W t le_rfl ht
  refine Submodule.finiteDimensional_of_le (S₂ := TypSp (Kf N K N) (Wf N W N) t.space) (Submodule.span_le.2 ?_)
  rintro φ ⟨hφ, hT⟩
  exact Submodule.subset_span ⟨hφ, fun u hu g => hT.1 u (Kf_top hu) g, fun g => lt_le_Wf (typeB_lt hT g)⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_mem_Sm' {N : ℕ} {f g : GA E N → ℂ} (hf : f ∈ Sm E N) (hg : g ∈ Sm E N) :
    (fun x => f x * g x) ∈ Sm E N := by
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  have h0 : oneL E N ∈ invSet E N := by
    have := val_mem_invSet (E := E) (1 : GL (Fin N) (Cinf E))
    rwa [Units.val_one] at this
  refine ((contDiffAt_chart hf x h0).mul (contDiffAt_chart hg x h0)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_invSet.mem_nhds h0] with y hy
  obtain ⟨u, hu⟩ := hy
  have hy' : y = toL (u : GL (Fin N) (Cinf E)).val := by rw [hu]; rfl
  rw [hy', chart_val, chart_val, chart_val]

theorem mult_flat {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : GlobalTheory.CompanionTheory.LimV.FlatFn (mult b γ) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.flat_absolute_character _ _
  | node t₁ t₂ ih₁ ih₂ => exact GlobalTheory.T.flat_node_function _ _ (ih₁ _) (ih₂ _)

theorem mult_rinv {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) (k : Kinf E N) {c : GL (Fin N) (Af E)}
    (hc : c ∈ Cint E N) : mult b γ (x * InducedTensorMap.cf N k c) = mult b γ x :=
  (mult_flat b γ).rinv x k c hc

theorem mult_node {r s : ℕ} (t₁ : Tr E r) (t₂ : Tr E s) (γ : ℕ → ℂ) (u : BlockIx (r + s) r → Ad E)
    (m : GA E r × GA E s) (k : Kinf E (r + s)) {c : GL (Fin (r + s)) (Af E)} (hc : c ∈ Cint E (r + s)) :
    mult (Tr.node t₁ t₂) γ (unip u * lev (Ad E) r s m * InducedTensorMap.cf (r + s) k c) =
      mult t₁ γ m.1 * mult t₂ (fun i => γ (i + t₁.twists.length)) m.2 :=
  GlobalTheory.T.node_function_levi_decomposition _ _ (mult_flat _ _) (mult_flat _ _) u m k c hc

theorem mult_ne {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) : mult b γ x ≠ 0 :=
  (mult_flat b γ).ne x

theorem mult_tendsto {N : ℕ} (b : Tr E N) (γ : ℕ → ℕ → ℂ) (hγ : ∀ i, Tendsto (fun k => γ k i) atTop (𝓝 0))
    (x : GA E N) : Tendsto (fun k => mult b (γ k) x) atTop (𝓝 1) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.tendsto_absolute_character_one _ x (fun k => γ k 0) (hγ 0)
  | node t₁ t₂ ih₁ ih₂ =>
    have h := (ih₁ γ hγ (GlobalTheory.CompanionTheory.LimV.leviOf x).1).mul
      (ih₂ (fun k i => γ k (i + t₁.twists.length)) (fun i => hγ _) (GlobalTheory.CompanionTheory.LimV.leviOf x).2)
    rw [one_mul] at h
    exact h

theorem mult_mem_Sm {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : mult b γ ∈ Sm E N :=
  (mult_flat b γ).sm

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem allLeaves_stable_of_disc {N : ℕ} (t : Tr E N) (h : t.Disc) : t.AllLeaves fun _ V => IsStable V := by
  induction t with
  | leaf V z =>
    rcases h with ⟨_, rfl, _⟩ | ⟨_, hV⟩
    · exact fun _ _ _ => Submodule.mem_top
    · exact hV.stable
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem disc_of_good {N : ℕ} (t : Tr E N) (h : t.Good) : t.Disc := by
  induction t with
  | leaf V z =>
    rcases h with h | ⟨h1, h2, _⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  | node t₁ t₂ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem allLeaves_strip {N : ℕ} (t : Tr E N) (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    t.strip.AllLeaves P ↔ t.AllLeaves P := by
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem allLeaves_addTw {N : ℕ} (t : Tr E N) (α : ℕ → ℂ) (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    (t.addTw α).AllLeaves P ↔ t.AllLeaves P := by
  induction t generalizing α with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ ih₁ ih₂ => exact and_congr (ih₁ _) (ih₂ _)

theorem strip_twists_length {N : ℕ} (t : Tr E N) : t.strip.twists.length = t.twists.length := by
  induction t with
  | leaf V z => rfl
  | node t₁ t₂ ih₁ ih₂ =>
    change (t₁.strip.twists ++ t₂.strip.twists).length = (t₁.twists ++ t₂.twists).length
    rw [List.length_append, List.length_append, ih₁, ih₂]

theorem addTw_congr {N : ℕ} (t : Tr E N) {α α' : ℕ → ℂ} (h : ∀ i < t.twists.length, α i = α' i) :
    t.addTw α = t.addTw α' := by
  induction t generalizing α α' with
  | leaf V z =>
    change Tr.leaf V (z + α 0) = Tr.leaf V (z + α' 0)
    rw [h 0 (by simp [Tr.twists])]
  | node t₁ t₂ ih₁ ih₂ =>
    have hl : (Tr.node t₁ t₂).twists.length = t₁.twists.length + t₂.twists.length := by
      change (t₁.twists ++ t₂.twists).length = _
      rw [List.length_append]
    change Tr.node (t₁.addTw α) (t₂.addTw fun i => α (i + t₁.twists.length)) =
      Tr.node (t₁.addTw α') (t₂.addTw fun i => α' (i + t₁.twists.length))
    rw [ih₁ (fun i hi => h i (by omega)), ih₂ (fun i hi => h (i + t₁.twists.length) (by omega))]

theorem eq_addTw {N : ℕ} (t : Tr E N) : t = t.strip.addTw fun i => t.twists.getD i 0 := by
  induction t with
  | leaf V z =>
    change Tr.leaf V z = Tr.leaf V (0 + z)
    rw [zero_add]
  | node t₁ t₂ ih₁ ih₂ =>
    change Tr.node t₁ t₂ = Tr.node (t₁.strip.addTw fun i => (t₁.twists ++ t₂.twists).getD i 0)
      (t₂.strip.addTw fun i => (t₁.twists ++ t₂.twists).getD (i + t₁.strip.twists.length) 0)
    have e₁ : t₁.strip.addTw (fun i => (t₁.twists ++ t₂.twists).getD i 0) =
        t₁.strip.addTw fun i => t₁.twists.getD i 0 := by
      refine addTw_congr _ fun i hi => ?_
      rw [strip_twists_length] at hi
      exact List.getD_append _ _ _ _ hi
    have e₂ : t₂.strip.addTw (fun i => (t₁.twists ++ t₂.twists).getD (i + t₁.strip.twists.length) 0) =
        t₂.strip.addTw fun i => t₂.twists.getD i 0 := by
      refine addTw_congr _ fun i _ => ?_
      rw [strip_twists_length, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel]
    rw [e₁, e₂, ← ih₁, ← ih₂]

def mulOp {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun φ := ⟨fun x => f x * φ.1 x, mul_mem_Sm' hf φ.2⟩
  map_add' φ ψ := Subtype.ext (funext fun x => by
    show f x * (φ.1 x + ψ.1 x) = f x * φ.1 x + f x * ψ.1 x
    ring)
  map_smul' c φ := Subtype.ext (funext fun x => by
    show f x * (c * φ.1 x) = c * (f x * φ.1 x)
    ring)

theorem mulOp_val {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) (φ : Sm E N) :
    (mulOp f hf φ).1 = fun x => f x * φ.1 x := rfl

theorem mulOp_mulChi {N : ℕ} (f : GA E N → ℂ) (hf : f ∈ Sm E N) (χ : HChar E) (ψ : Sm E N) :
    mulOp f hf (mulChi N χ ψ) = mulChi N χ (mulOp f hf ψ) := Subtype.ext (funext fun x => by
  show f x * (mulChi N χ ψ).1 x = (mulChi N χ (mulOp f hf ψ)).1 x
  rw [mulChi_apply, mulChi_apply]
  show f x * (ψ.1 x * _) = (f x * ψ.1 x) * _
  ring)

theorem mult_node_unip {r s : ℕ} (t₁ : Tr E r) (t₂ : Tr E s) (γ : ℕ → ℂ) (u : BlockIx (r + s) r → Ad E)
    (x : GA E (r + s)) : mult (Tr.node t₁ t₂) γ (unip u * x) = mult (Tr.node t₁ t₂) γ x := by
  obtain ⟨q, hc, hx⟩ := exists_decI (r := r) (s := s) x
  rw [hx, ← mul_assoc, ← mul_assoc, ← InducedTensorMap.D.unip_add', mult_node _ _ _ _ _ _ hc, mult_node _ _ _ _ _ _ hc]

theorem finGL_unip' {r s : ℕ} (x : BlockIx (r + s) r → Af E) :
    finGL E (r + s) (unip x) = unip fun p => sFin E (x p) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_unip]
    have h0 : (fun p => pInf E (sFin E (x p))) = 0 := funext fun p => map_zero (infEq E).symm
    rw [h0, InducedTensorMap.unip_zero]
  · rw [pFin_finGL, IwaAd.map_unip]
    rfl

theorem lev_mul_cf_int {r s : ℕ} (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ (mf : GL (Fin r) (Af E) × GL (Fin s) (Af E)) (c : GL (Fin (r + s)) (Af E)), c ∈ Cint E (r + s) ∧
      ∀ m : GA E r × GA E s, ∃ v : BlockIx (r + s) r → Ad E,
        lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g) =
          unip v * lev (Ad E) r s (m.1 * finGL E r mf.1, m.2 * finGL E s mf.2) * InducedTensorMap.cf (r + s) k c := by
  obtain ⟨xf, mf, c, hc, hg⟩ := IwaFin.exists_unip_lev_integral E r s g
  refine ⟨mf, c, hc, fun m => ?_⟩
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m fun p => sFin E (xf p)
  refine ⟨v, ?_⟩
  have h1 : infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g =
      (unip fun p => sFin E (xf p)) * lev (Ad E) r s (finGL E r mf.1, finGL E s mf.2) *
        InducedTensorMap.cf (r + s) k c := by
    calc infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g
        = infGL E (r + s) (Unitary.toUnits k) * (finGL E (r + s) (unip xf * lev (Af E) r s mf) *
            finGL E (r + s) c) := by rw [hg, map_mul]
      _ = finGL E (r + s) (unip xf * lev (Af E) r s mf) *
            (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) c) := by
          rw [← mul_assoc, infGL_comm, mul_assoc]
      _ = _ := by
          rw [map_mul, finGL_unip', Slice1.lev_finGL]
          rfl
  rw [h1, ← mul_assoc, ← mul_assoc, hv, mul_assoc (unip v), ← map_mul]
  rfl

theorem act_fin_apply' {N : ℕ} (g : GL (Fin N) (Af E)) (φ : Sm E N) (x : GA E N) :
    (act (.fin g) φ).1 x = φ.1 (x * finGL E N g) := rfl

theorem mult_operator_shifts_twist {N : ℕ} (b : Tr E N) : ∀ (α β : ℕ → ℂ), (b.AllLeaves fun _ V => IsStable V) →
    ∀ φ ∈ (b.addTw α).space, mulOp (mult b fun i => β i - α i) (mult_mem_Sm b _) φ ∈ (b.addTw β).space := by
  induction b with
  | leaf V z =>
    intro α β _
    rintro _ ⟨ψ, hψ, rfl⟩
    refine ⟨ψ, hψ, Subtype.ext (funext fun x => ?_)⟩
    change ((mulChi _ (Model.absC E (z + β 0))) ψ).1 x =
      mult (Tr.leaf V z) (fun i => β i - α i) x * ((mulChi _ (Model.absC E (z + α 0))) ψ).1 x
    rw [mult_leaf, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
      ExponentTwist.chiDet_absC_val]
    have e : ∀ L : ℂ, Complex.exp ((z + β 0) * L) =
        Complex.exp ((β 0 - α 0) * L) * Complex.exp ((z + α 0) * L) := fun L => by
      rw [← Complex.exp_add]
      ring_nf
    rw [e]
    ring
  | @node r s t₁ t₂ ih₁ ih₂ =>
    intro α β hb φ hφ
    obtain ⟨hb₁, hb₂⟩ := hb
    set L := t₁.twists.length with hL
    set α' : ℕ → ℂ := fun i => α (i + L) with hα'
    set β' : ℕ → ℂ := fun i => β (i + L) with hβ'
    have hU₁ : IsStable (t₁.addTw α).space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₁)
    have hU₁' : IsStable (t₁.addTw β).space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₁)
    have hU₂ : IsStable (t₂.addTw α').space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₂)
    have hU₂' : IsStable (t₂.addTw β').space := Trees.isStable_space _ ((allLeaves_addTw _ _ _).2 hb₂)

    have hA : ∀ (z : ℂ) (h : GL (Fin r) (Af E)), ∀ ψ ∈ tw (t₁.addTw α).space z, ∃ χ ∈ tw (t₁.addTw β).space z,
        χ.1 = fun m => mult t₁ (fun i => β i - α i) (m * finGL E r h) * ψ.1 m := by
      intro z h ψ hψ
      have h1 : act (.fin h⁻¹) ψ ∈ tw (t₁.addTw α).space z := ParabolicProjection.isStable_tw hU₁ z _ _ hψ
      obtain ⟨ρ, hρ, hρe⟩ := h1
      have h2 : mulOp (mult t₁ fun i => β i - α i) (mult_mem_Sm t₁ _) (act (.fin h⁻¹) ψ) ∈
          tw (t₁.addTw β).space z := by
        rw [← hρe]
        show mulOp _ _ ((mulChi r (Model.absC E z)) ρ) ∈ _
        rw [mulOp_mulChi]
        exact ⟨_, ih₁ α β hb₁ ρ hρ, rfl⟩
      refine ⟨act (.fin h) (mulOp (mult t₁ fun i => β i - α i) (mult_mem_Sm t₁ _) (act (.fin h⁻¹) ψ)),
        ParabolicProjection.isStable_tw hU₁' z _ _ h2, funext fun m => ?_⟩
      simp only [act_fin_apply', mulOp_val]
      rw [mul_assoc m, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hB : ∀ (z : ℂ) (h : GL (Fin s) (Af E)), ∀ ψ ∈ tw (t₂.addTw α').space z, ∃ χ ∈ tw (t₂.addTw β').space z,
        χ.1 = fun m => mult t₂ (fun i => β' i - α' i) (m * finGL E s h) * ψ.1 m := by
      intro z h ψ hψ
      have h1 : act (.fin h⁻¹) ψ ∈ tw (t₂.addTw α').space z := ParabolicProjection.isStable_tw hU₂ z _ _ hψ
      obtain ⟨ρ, hρ, hρe⟩ := h1
      have h2 : mulOp (mult t₂ fun i => β' i - α' i) (mult_mem_Sm t₂ _) (act (.fin h⁻¹) ψ) ∈
          tw (t₂.addTw β').space z := by
        rw [← hρe]
        show mulOp _ _ ((mulChi s (Model.absC E z)) ρ) ∈ _
        rw [mulOp_mulChi]
        exact ⟨_, ih₂ α' β' hb₂ ρ hρ, rfl⟩
      refine ⟨act (.fin h) (mulOp (mult t₂ fun i => β' i - α' i) (mult_mem_Sm t₂ _) (act (.fin h⁻¹) ψ)),
        ParabolicProjection.isStable_tw hU₂' z _ _ h2, funext fun m => ?_⟩
      simp only [act_fin_apply', mulOp_val]
      rw [mul_assoc m, ← map_mul, mul_inv_cancel, map_one, mul_one]
    set Φ := mult (Tr.node t₁ t₂) fun i => β i - α i with hΦ
    have hΦS : Φ ∈ Sm E (r + s) := mult_mem_Sm _ _
    change φ ∈ Submodule.span ℂ _ at hφ
    change _ ∈ Submodule.span ℂ _
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨⟨hu, hsl⟩, hK⟩ := h
      refine Submodule.subset_span ⟨⟨fun x g => ?_, fun k g => ?_⟩, ?_⟩
      · change Φ (unip x * g) * φ.1 (unip x * g) = Φ g * φ.1 g
        rw [hΦ, mult_node_unip, hu x g]
      · obtain ⟨mf, c, hc, hdec⟩ := lev_mul_cf_int (r := r) (s := s) k g
        obtain ⟨n, ψ₁, ψ₂, h₁, h₂, e⟩ := InducedTensorMap.tensor_pair_finite_sum (hsl k g)
        choose χ₁ hχ₁ eχ₁ using fun i => hA _ mf.1 (ψ₁ i) (h₁ i)
        choose χ₂ hχ₂ eχ₂ using fun i => hB _ mf.2 (ψ₂ i) (h₂ i)
        have key := ParabolicProjection.sum_mem_tens2 (V₁ := tw (t₁.addTw β).space ((s : ℂ) / 2))
          (V₂ := tw (t₂.addTw β').space (-(r : ℂ) / 2)) hχ₁ hχ₂
        convert key using 1
        funext m
        obtain ⟨v, hv⟩ := hdec m
        have e2 := congrFun e m
        try simp only at e2
        change Φ (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) *
          φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = _
        rw [e2, hv, hΦ, mult_node _ _ _ _ _ _ hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eχ₁ i, eχ₂ i]
        ring
      · have hK' : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k φ)) := hK
        change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (r + s) k (mulOp Φ hΦS φ)))
        have e : (Set.range fun k => cptRep E (r + s) k (mulOp Φ hΦS φ)) =
            (mulOp Φ hΦS) '' Set.range fun k => cptRep E (r + s) k φ := by
          rw [← Set.range_comp]
          congr 1
          funext k
          refine Subtype.ext (funext fun x => ?_)
          change Φ (x * infGL E (r + s) (Unitary.toUnits k)) * φ.1 (x * infGL E (r + s) (Unitary.toUnits k)) =
            Φ x * φ.1 (x * infGL E (r + s) (Unitary.toUnits k))
          have e1 : x * infGL E (r + s) (Unitary.toUnits k) = x * InducedTensorMap.cf (r + s) k 1 := by
            simp [InducedTensorMap.cf]
          rw [e1, hΦ, mult_rinv _ _ _ _ (one_mem _)]
        rw [e, Submodule.span_image]
        infer_instance
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem flat {N : ℕ} (b : Tr E N) (hb : b.AllLeaves fun _ V => IsStable V) (α β : ℕ → ℂ) (φ : Sm E N)
    (hφ : φ ∈ (b.addTw α).space) :
    ∃ ψ ∈ (b.addTw β).space, ψ.1 = fun x => mult b (fun i => β i - α i) x * φ.1 x :=
  ⟨_, mult_operator_shifts_twist b α β hb φ hφ, rfl⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem heckeAct_smul {a b : ℕ} {ι : Type} [Fintype ι] (h : HeckeM E a b ι) (c : ℂ) (f : ι → H E a b → ℂ) :
    heckeAct h (c • f) = c • heckeAct h f := by
  funext i x
  simp only [heckeAct, Pi.smul_apply, smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => ?_
  ring

theorem tendsto_heckeAct {a b : ℕ} {ι : Type} [Fintype ι] (h : HeckeM E a b ι) {F : ℕ → ι → H E a b → ℂ}
    {F₀ : ι → H E a b → ℂ} (hF : ∀ i x, Tendsto (fun k => F k i x) atTop (𝓝 (F₀ i x))) (i : ι) (x : H E a b) :
    Tendsto (fun k => heckeAct h (F k) i x) atTop (𝓝 (heckeAct h F₀ i x)) := by
  simp only [heckeAct, Finsupp.sum]
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun g _ => (hF j _).const_mul _

theorem fd_prodSpan {X Y : Type} (W₁ : Submodule ℂ (X → ℂ)) (W₂ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W₁]
    [FiniteDimensional ℂ W₂] :
    FiniteDimensional ℂ (Submodule.span ℂ {f : X × Y → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) := by
  let B : W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] (X × Y → ℂ) :=
    LinearMap.mk₂ ℂ (fun w₁ w₂ k => (w₁ : X → ℂ) k.1 * (w₂ : Y → ℂ) k.2)
      (fun _ _ _ => by funext k; simp [add_mul]) (fun _ _ _ => by funext k; simp [mul_assoc])
      (fun _ _ _ => by funext k; simp [mul_add]) (fun _ _ _ => by funext k; simp [mul_left_comm])
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift B)) (Submodule.span_le.2 ?_)
  rintro _ ⟨w₁, h₁, w₂, h₂, rfl⟩
  exact ⟨TensorProduct.tmul ℂ (⟨w₁, h₁⟩ : W₁) (⟨w₂, h₂⟩ : W₂), by simp [B]⟩

theorem mul_mem_pairSpace {a b : ℕ} {U₁ U₁' : Submodule ℂ (Sm E a)} {U₂ U₂' : Submodule ℂ (Sm E b)}
    (M₁ : GA E a → ℂ) (M₂ : GA E b → ℂ) (h₁ : ∀ φ ∈ U₁, ∃ ψ ∈ U₁', ψ.1 = fun x => M₁ x * φ.1 x)
    (h₂ : ∀ φ ∈ U₂, ∃ ψ ∈ U₂', ψ.1 = fun x => M₂ x * φ.1 x) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) :
    (fun x => (M₁ x.1 * M₂ x.2) * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩ := hF
    obtain ⟨ψ₁, hψ₁, e₁⟩ := h₁ φ₁ hφ₁
    obtain ⟨ψ₂, hψ₂, e₂⟩ := h₂ φ₂ hφ₂
    refine Submodule.subset_span ⟨ψ₁, hψ₁, ψ₂, hψ₂, ?_⟩
    funext x
    rw [e₁, e₂]
    ring
  | zero =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (0 : H E a b → ℂ) x) = 0 := by funext x; simp
    rw [e]
    exact Submodule.zero_mem _
  | add F G _ _ hF hG =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (F + G) x) =
        (fun x => (M₁ x.1 * M₂ x.2) * F x) + fun x => (M₁ x.1 * M₂ x.2) * G x := by
      funext x; simp [mul_add]
    rw [e]
    exact Submodule.add_mem _ hF hG
  | smul c F _ hF =>
    have e : (fun x : H E a b => (M₁ x.1 * M₂ x.2) * (c • F) x) = c • fun x => (M₁ x.1 * M₂ x.2) * F x := by
      funext x; simp [mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ c hF

theorem cf_one_left (n : ℕ) (c : GL (Fin n) (Af E)) : InducedTensorMap.cf n 1 c = finGL E n c := by
  simp [InducedTensorMap.cf]

theorem cf_one_right (n : ℕ) (k : Kinf E n) : InducedTensorMap.cf n k 1 = infGL E n (Unitary.toUnits k) := by
  simp [InducedTensorMap.cf]

theorem limVec : LimVec := by
  intro hA E _ _ _ a b ι _ t₁ t₂ s₁ s₂ K₁ K₂ W₁ W₂ C lam lam₀ f hK₁ hK₂ hW₁ hW₂ _hC hs₁ hs₂ ht₁ ht₂ hst₁ hst₂
    hz₁ hz₂ hf0 hfP hfT hEig hLam
  classical

  have et₁ : ∀ k, t₁ k = s₁.strip.addTw fun i => (t₁ k).twists.getD i 0 := fun k =>
    (eq_addTw (t₁ k)).trans (by rw [hst₁ k])
  have et₂ : ∀ k, t₂ k = s₂.strip.addTw fun i => (t₂ k).twists.getD i 0 := fun k =>
    (eq_addTw (t₂ k)).trans (by rw [hst₂ k])
  have es₁ : s₁ = s₁.strip.addTw fun i => s₁.twists.getD i 0 := eq_addTw s₁
  have es₂ : s₂ = s₂.strip.addTw fun i => s₂.twists.getD i 0 := eq_addTw s₂
  have hd₁ : s₁.Disc := disc_of_good s₁ hs₁
  have hd₂ : s₂.Disc := disc_of_good s₂ hs₂
  have hb₁ : s₁.strip.AllLeaves fun _ V => IsStable V := (allLeaves_strip s₁ _).2 (allLeaves_stable_of_disc s₁ hd₁)
  have hb₂ : s₂.strip.AllLeaves fun _ V => IsStable V := (allLeaves_strip s₂ _).2 (allLeaves_stable_of_disc s₂ hd₂)

  let γ₁ : ℕ → ℕ → ℂ := fun k i => s₁.twists.getD i 0 - (t₁ k).twists.getD i 0
  let γ₂ : ℕ → ℕ → ℂ := fun k i => s₂.twists.getD i 0 - (t₂ k).twists.getD i 0
  have hγ₁ : ∀ i, Tendsto (fun k => γ₁ k i) atTop (𝓝 0) := fun i => by
    have := (tendsto_const_nhds (x := s₁.twists.getD i 0)).sub (hz₁ i)
    rwa [sub_self] at this
  have hγ₂ : ∀ i, Tendsto (fun k => γ₂ k i) atTop (𝓝 0) := fun i => by
    have := (tendsto_const_nhds (x := s₂.twists.getD i 0)).sub (hz₂ i)
    rwa [sub_self] at this
  let Φ : ℕ → H E a b → ℂ := fun k x => mult s₁.strip (γ₁ k) x.1 * mult s₂.strip (γ₂ k) x.2
  have hΦne : ∀ k x, Φ k x ≠ 0 := fun k x => mul_ne_zero (mult_ne _ _ _) (mult_ne _ _ _)
  have hΦlim : ∀ x, Tendsto (fun k => Φ k x) atTop (𝓝 1) := fun x => by
    have := (mult_tendsto s₁.strip γ₁ hγ₁ x.1).mul (mult_tendsto s₂.strip γ₂ hγ₂ x.2)
    rwa [one_mul] at this

  let K₁' : Subgroup (GL (Fin a) (Af E)) := K₁ ⊓ Cint E a
  let K₂' : Subgroup (GL (Fin b) (Af E)) := K₂ ⊓ Cint E b
  have hK₁' : IsOpen (K₁' : Set (GL (Fin a) (Af E))) :=
    hK₁.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hK₂' : IsOpen (K₂' : Set (GL (Fin b) (Af E))) :=
    hK₂.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E b)
  haveI := hW₁
  haveI := hW₂
  haveI : FiniteDimensional ℂ (TypSp K₁' W₁ s₁.space) := fd_typSp hA s₁ hd₁ K₁' hK₁' W₁
  haveI : FiniteDimensional ℂ (TypSp K₂' W₂ s₂.space) := fd_typSp hA s₂ hd₂ K₂' hK₂' W₂
  let X₀ : Submodule ℂ (H E a b → ℂ) := pairSpace (TypSp K₁' W₁ s₁.space) (TypSp K₂' W₂ s₂.space)
  haveI : FiniteDimensional ℂ X₀ := fd_tens2 _ _

  have hmul₁ : ∀ k, ∀ φ ∈ (t₁ k).space, ∃ ψ ∈ s₁.space, ψ.1 = fun x => mult s₁.strip (γ₁ k) x * φ.1 x := by
    intro k φ hφ
    rw [et₁ k] at hφ
    obtain ⟨ψ, hψ, e⟩ := flat s₁.strip hb₁ _ (fun i => s₁.twists.getD i 0) φ hφ
    exact ⟨ψ, by rw [es₁]; exact hψ, e⟩
  have hmul₂ : ∀ k, ∀ φ ∈ (t₂ k).space, ∃ ψ ∈ s₂.space, ψ.1 = fun x => mult s₂.strip (γ₂ k) x * φ.1 x := by
    intro k φ hφ
    rw [et₂ k] at hφ
    obtain ⟨ψ, hψ, e⟩ := flat s₂.strip hb₂ _ (fun i => s₂.twists.getD i 0) φ hφ
    exact ⟨ψ, by rw [es₂]; exact hψ, e⟩
  have hg : ∀ k i, (fun x => Φ k x * f k i x) ∈ X₀ := by
    intro k i
    refine pair_typ (mul_mem_pairSpace _ _ (hmul₁ k) (hmul₂ k) (hfP k i)) ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩
    · have e₁ : x.1 * finGL E a u₁ = x.1 * InducedTensorMap.cf a 1 u₁ := by rw [cf_one_left]
      have e₂ : x.2 * finGL E b u₂ = x.2 * InducedTensorMap.cf b 1 u₂ := by rw [cf_one_left]
      show mult s₁.strip (γ₁ k) (x.1 * finGL E a u₁) * mult s₂.strip (γ₂ k) (x.2 * finGL E b u₂) *
          f k i (x * (finGL E a u₁, finGL E b u₂)) = Φ k x * f k i x
      rw [e₁, e₂, mult_rinv _ _ _ _ hu₁.2, mult_rinv _ _ _ _ hu₂.2, (hfT k i).1 u₁ hu₁.1 u₂ hu₂.1 x]
    · have e : (fun kk : Kinf E a × Kinf E b =>
          Φ k (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))) *
            f k i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2)))) =
          Φ k x • fun kk : Kinf E a × Kinf E b =>
            f k i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))) := by
        funext kk
        have e₁ : x.1 * infGL E a (Unitary.toUnits kk.1) = x.1 * InducedTensorMap.cf a kk.1 1 := by rw [cf_one_right]
        have e₂ : x.2 * infGL E b (Unitary.toUnits kk.2) = x.2 * InducedTensorMap.cf b kk.2 1 := by rw [cf_one_right]
        show mult s₁.strip (γ₁ k) (x.1 * infGL E a (Unitary.toUnits kk.1)) *
            mult s₂.strip (γ₂ k) (x.2 * infGL E b (Unitary.toUnits kk.2)) * _ = _
        rw [e₁, e₂, mult_rinv _ _ _ _ (one_mem _), mult_rinv _ _ _ _ (one_mem _)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ ((hfT k i).2 x)

  let V := ι → X₀
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  let gk : ℕ → V := fun k i => ⟨fun x => Φ k x * f k i x, hg k i⟩
  have hgk0 : ∀ k, gk k ≠ 0 := by
    intro k h0
    apply hf0 k
    funext i x
    have := congrArg (fun v : V => ((v i : X₀) : H E a b → ℂ) x) h0
    simp only [gk] at this
    exact (mul_eq_zero.1 this).resolve_left (hΦne k x)
  let c : ℕ → ℂ := fun k => ((‖e (gk k)‖⁻¹ : ℝ) : ℂ)
  let v : ℕ → (Fin (Module.finrank ℂ V) → ℂ) := fun k => c k • e (gk k)
  have hv : ∀ k, v k ∈ Metric.sphere (0 : Fin (Module.finrank ℂ V) → ℂ) 1 := by
    intro k
    have hne : e (gk k) ≠ 0 := (LinearEquiv.map_ne_zero_iff e).2 (hgk0 k)
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ V) → ℂ) 1).tendsto_subseq hv
  let u : V := e.symm w
  have hu0 : u ≠ 0 := by
    intro h0
    have : w = 0 := by simpa [u] using congrArg e h0
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at hw
    exact zero_ne_one hw
  let F : ι → H E a b → ℂ := fun i x => ((u i : X₀) : H E a b → ℂ) x

  have hA' : ∀ i x, Tendsto (fun k => c (φ k) * (Φ (φ k) x * f (φ k) i x)) atTop (𝓝 (F i x)) := by
    intro i x
    let L : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] ℂ :=
      (LinearMap.proj x) ∘ₗ X₀.subtype ∘ₗ (LinearMap.proj i) ∘ₗ e.symm.toLinearMap
    have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
    have h1 := (hL.tendsto w).comp hlim
    refine h1.congr fun k => ?_
    show L (v (φ k)) = _
    show ((e.symm (c (φ k) • e (gk (φ k)))) i : H E a b → ℂ) x = _
    rw [map_smul, LinearEquiv.symm_apply_apply]
    rfl
  have hconv : ∀ i x, Tendsto (fun k => c (φ k) * f (φ k) i x) atTop (𝓝 (F i x)) := by
    intro i x
    have h1 := (hA' i x).div ((hΦlim x).comp hφ.tendsto_atTop) one_ne_zero
    rw [div_one] at h1
    refine h1.congr fun k => ?_
    show c (φ k) * (Φ (φ k) x * f (φ k) i x) / Φ (φ k) x = _
    rw [mul_left_comm, mul_div_cancel_left₀ _ (hΦne _ x)]
  refine ⟨F, ?_, fun i => ?_, fun i => ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩, fun h hh => ?_⟩
  · intro hF0
    apply hu0
    funext i
    exact Subtype.ext (funext fun x => congrFun (congrFun hF0 i) x)
  · exact tensor_span_mono (typSp_le _ _ _) (typSp_le _ _ _) (u i).2
  · refine tendsto_nhds_unique ((hconv i _).congr fun k => ?_) (hconv i x)
    rw [(hfT (φ k) i).1 u₁ hu₁ u₂ hu₂ x]
  · let Z : Submodule ℂ (Kinf E a × Kinf E b → ℂ) :=
      Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}
    haveI : FiniteDimensional ℂ Z := fd_prodSpan W₁ W₂
    refine (Submodule.closed_of_finiteDimensional Z).mem_of_tendsto
      (tendsto_pi_nhds.2 fun kk => hconv i (x * (infGL E a (Unitary.toUnits kk.1), infGL E b (Unitary.toUnits kk.2))))
      (Eventually.of_forall fun k => ?_)
    exact Z.smul_mem (c (φ k)) ((hfT (φ k) i).2 x)
  · funext i x
    have h1 := tendsto_heckeAct h hconv i x
    have h2 : ∀ k, heckeAct h (fun i x => c (φ k) * f (φ k) i x) i x = lam (φ k) h * (c (φ k) * f (φ k) i x) := by
      intro k
      rw [show (fun i x => c (φ k) * f (φ k) i x) = c (φ k) • f (φ k) from rfl, heckeAct_smul, hEig (φ k) h hh]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have h3 := ((hLam h hh).comp hφ.tendsto_atTop).mul (hconv i x)
    have := tendsto_nhds_unique (h1.congr h2) h3
    simpa only [Pi.smul_apply, smul_eq_mul] using this

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
end
