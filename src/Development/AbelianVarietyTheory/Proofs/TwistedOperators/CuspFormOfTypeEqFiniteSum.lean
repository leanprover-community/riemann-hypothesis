import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem pairwise_commute {θ : InfFam D} {V : HSp D} {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ((Finset.univ : Finset D.what₂.Tau) : Set D.what₂.Tau).Pairwise
      (Function.onFun Commute fun τ => atTau θ V τ (g τ)) :=
  fun τ _ τ' _ hne => GlobalTheory.PointAtPlaceComm.atTau_comm D θ h.1 V τ τ' hne _ (h.2 τ) _ (h.2 τ')

def realProd (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then
    Finset.univ.noncommProd (fun τ => atTau θ V τ (g τ)) (pairwise_commute h)
  else 1

variable {θ : InfFam D} {V : HSp D}

theorem update_mem {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) (τ : D.what₂.Tau) :
    Function.update g τ₀ g' τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  by_cases h : τ = τ₀
  · subst h; rw [Function.update_self]; exact hg'
  · rw [Function.update_of_ne h]; exact hg τ

theorem realProd_update (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    realProd θ V (Function.update g τ₀ g') = atTau θ V τ₀ g' * realProd θ V (Function.update g τ₀ 1) := by
  classical
  have h1 := update_mem hg τ₀ hg'
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dif_pos ⟨hθ, h1⟩, dif_pos ⟨hθ, h2⟩, ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀),
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀) (fun τ => atTau θ V τ (Function.update g τ₀ 1 τ))]
  simp only [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ, one_mul]
  congr 1
  refine Finset.noncommProd_congr rfl (fun τ hτ => ?_) _
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ), Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem realProd_commute (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    Commute (atTau θ V τ₀ g') (realProd θ V (Function.update g τ₀ 1)) := by
  classical
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dif_pos ⟨hθ, h2⟩]
  refine Finset.noncommProd_commute _ _ _ _ fun τ _ => ?_
  by_cases h : τ = τ₀
  · subst h
    rw [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact Commute.one_right _
  · exact GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ₀ τ (Ne.symm h) _ hg' _ (h2 τ)

theorem realProd_one (hθ : IsInfFam θ) : realProd θ V (fun _ => 1) = 1 := by
  unfold realProd
  rw [dif_pos ⟨hθ, fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _⟩]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun τ _ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ, one_pow]

theorem isAutFunSm_realProd (hθ : IsInfFam θ) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V (realProd θ V g) φ) := by
  unfold realProd
  split_ifs with h
  · refine Finset.noncommProd_induction _ _ _ (fun x => ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (rTr V x ψ))
      (fun a b ha hb ψ hψ => ?_) (fun ψ hψ => ?_) (fun τ _ ψ hψ => ?_) φ hφ
    · have e : rTr V (a * b) ψ = rTr V a (rTr V b ψ) := funext fun x => by simp only [rTr, mul_assoc]
      rw [e]; exact ha _ (hb _ hψ)
    · have e : rTr V 1 ψ = ψ := funext fun x => by simp only [rTr, mul_one]
      rw [e]; exact hψ
    · exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V ψ hψ τ _ (h.2 τ)
  · have e : rTr V 1 φ = φ := funext fun x => by simp only [rTr, mul_one]
    rw [e]; exact hφ

theorem rep_mul {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  unfold DSModel.rep
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg) _
    (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hh)

theorem rep_one {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem sm_eq_top {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] :
    M.sm τ = ⊤ := by
  rw [GlobalTheory.SmVec.sm_eq]
  refine Submodule.orthogonal_eq_bot_iff.1 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
  exact GlobalTheory.SmVec.eq_zero_of_inner_smooth (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    fun u hu => (Submodule.mem_orthogonal _ _).1 hy u hu

theorem equiv_one {H G : Type} [AddCommGroup H] [Module ℂ H] [Module.Free ℂ H] [Module.Finite ℂ H] [Mul G]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    {m : ℕ} (k : Fin m → G) (hk : ∀ j, k j ∈ K) (B : Fin m → (H →ₗ[ℂ] H))
    (hB : ∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j)
    (f : G → ℂ) (hf : ∀ g ∈ K, f g = ∑ j, f (k j) * LinearMap.trace ℂ H (ρ g ∘ₗ B j))
    (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K) (e : H →ₗ[ℂ] ℂ) (v : H) {h : G} (hh : h ∈ K) :
    ∑ j, e (B j (ρ h v)) * f (k j) = ∑ j, e (B j v) * f (h * k j) := by
  have e1 : ∀ j, f (h * k j) = ∑ i, f (k i) * LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) := by
    intro j
    rw [hf _ (hmul _ hh _ (hk j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ _ hh _ (hk j), LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have e2 : ∀ i, e (B i (ρ h v)) = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) * e (B j v) := by
    intro i
    have := congrArg (fun L : H →ₗ[ℂ] H => e (L v)) (hB i h hh)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul] at this
    exact this
  simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.DefiniteDecomp
end
end

section
section
open Module

namespace GlobalTheory.DualFrameSpan

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma sum_comp' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]

lemma comp_sum' {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]

lemma eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by
  set b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, (inner ℂ (b i) ((LinearMap.adjoint B ∘ₗ B) (b i)) : ℂ)
      = ((‖B (b i)‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast; first | rfl | simp | norm_cast
  simp_rw [h'] at h
  have h2 : (∑ i, ‖B (b i)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h2
  apply b.toBasis.ext
  intro i
  have := h3 i (Finset.mem_univ _)
  simpa using this

noncomputable def pairing (W : Submodule ℂ (H →ₗ[ℂ] H)) : LinearMap.BilinForm ℂ W :=
  LinearMap.mk₂ ℂ (fun X Y : W => LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)))
    (fun x y z => by simp [LinearMap.add_comp]) (fun c x y => by simp [LinearMap.smul_comp])
    (fun x y z => by simp [LinearMap.comp_add]) (fun c x y => by simp [LinearMap.comp_smul])

lemma pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl

lemma pairing_nondegenerate (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y

section span

variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

lemma adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨g', hg', he⟩ := hadj g hg
    rw [he]; exact Submodule.subset_span ⟨g', hg', rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

lemma comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [← hρ g hg h hh]; exact Submodule.subset_span ⟨_, hmul g hg h hh, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [LinearMap.add_comp]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.smul_comp]; exact Submodule.smul_mem _ _ hx

end span

theorem dual_frame : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  intro G H _ _ _ _ K ρ hmul hρ hadj
  classical
  obtain ⟨t, hts, hsp, hli⟩ := exists_linearIndependent ℂ (ρ '' K)
  set W := Submodule.span ℂ (ρ '' K) with hWdef
  have hWt : Submodule.span ℂ (Set.range ((↑) : t → (H →ₗ[ℂ] H))) = W := by
    rw [Subtype.range_coe]; exact hsp
  haveI : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b0 : Basis t ℂ W := (Basis.span hli).map (LinearEquiv.ofEq _ _ hWt)
  let e := Fintype.equivFin t
  let b : Basis (Fin (Fintype.card t)) ℂ W := b0.reindex e
  have hb : ∀ j, ((b j : W) : H →ₗ[ℂ] H) = ((e.symm j : t) : H →ₗ[ℂ] H) := by
    intro j; simp [b, b0, Basis.span_apply]
  have hbK : ∀ j, ∃ g ∈ K, ρ g = (b j : H →ₗ[ℂ] H) := fun j => by
    rw [hb]; exact hts (e.symm j).2
  choose k hkK hk using hbK
  have hnd := pairing_nondegenerate W (fun X hX => adjoint_mem_span K ρ hadj hX)
  let D := (pairing W).dualBasis hnd b
  have expand : ∀ X ∈ W, X = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ X) • (D j : H →ₗ[ℂ] H) := by
    intro X hX
    have h1 := congrArg Subtype.val (D.sum_repr ⟨X, hX⟩)
    rw [Submodule.coe_sum] at h1
    change _ = X at h1
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, LinearMap.BilinForm.dualBasis_repr_apply, pairing_apply, hk,
      LinearMap.trace_comp_comm' (b j : H →ₗ[ℂ] H) X]
  have hdual : ∀ i j, LinearMap.trace ℂ H (ρ (k i) ∘ₗ (D j : H →ₗ[ℂ] H)) = if i = j then 1 else 0 := by
    intro i j
    rw [hk, LinearMap.trace_comp_comm']
    exact LinearMap.BilinForm.apply_dualBasis_left hnd b j i
  refine ⟨Fintype.card t, k, fun j => (D j : H →ₗ[ℂ] H), hkK, ?_, ?_⟩
  · intro A g hg
    set A' := ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) • (D j : H →ₗ[ℂ] H) with hA'
    have hbi : ∀ i, LinearMap.trace ℂ H (ρ (k i) ∘ₗ A') = LinearMap.trace ℂ H (ρ (k i) ∘ₗ A) := by
      intro i
      simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, hdual, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hvan : ∀ C ∈ W, LinearMap.trace ℂ H (C ∘ₗ A') = LinearMap.trace ℂ H (C ∘ₗ A) := by
      intro C hC
      have h1 := congrArg Subtype.val (b.sum_repr ⟨C, hC⟩)
      rw [Submodule.coe_sum] at h1
      change _ = C at h1
      rw [← h1]
      simp only [Submodule.coe_smul, sum_comp', LinearMap.smul_comp, map_sum, map_smul, ← hk, hbi]
    rw [← hvan (ρ g) (Submodule.subset_span ⟨g, hg, rfl⟩)]
    simp only [A', comp_sum', LinearMap.comp_smul, map_sum, map_smul, smul_eq_mul]
  · intro i h hh
    exact expand _ (comp_mem_span K ρ hmul hρ hh (D i).2)

end GlobalTheory.DualFrameSpan
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_frame_span_unitary_representation : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  atlas_forward_decl GlobalTheory.DualFrameSpan.dual_frame
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

namespace GlobalTheory.RepAdj

theorem rep_adjoint_eq_inv : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  intro D V S M τ _ g hg
  have hfd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self (M.ε τ))
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact ((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ |>.mul (M.fr_unit τ)
  have hgi : g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := GlobalTheory.SmVec.inv_mem_UH hG hg
  have hgu : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmVec.isUnit_of_mem_UH hG hg)
  refine ⟨hgi, ?_⟩
  have hU := (M.ds τ).2.2.1
  have m1 : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg
  have m2 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
    GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hgi
  have hprod : (M.fr τ * g⁻¹ * (M.fr τ)⁻¹) * (M.fr τ * g * (M.fr τ)⁻¹) = 1 := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hfd]
    rw [← Matrix.mul_assoc g⁻¹ g, Matrix.nonsing_inv_mul _ hgu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hfd]
  have hcomp : ∀ x, M.rep τ g⁻¹ (M.rep τ g x) = x := by
    intro x
    have := hU.1.2 _ m2 _ m1
    rw [hprod, hU.1.1] at this
    have hx := congrArg (fun T : M.H τ →L[ℂ] M.H τ => T x) this
    simpa [DSModel.rep] using hx.symm
  have hiso : ∀ x y, inner ℂ (M.rep τ g⁻¹ x) (M.rep τ g⁻¹ y) = inner ℂ x y := by
    have hn : ∀ v, ‖(M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) v‖ = ‖v‖ := fun v => hU.2.1 _ m2 v
    intro x y
    exact (LinearMap.norm_map_iff_inner_map_map (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ)).1 hn x y
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  have := hiso x (M.rep τ g y)
  rw [hcomp] at this
  simpa using this

end GlobalTheory.RepAdj
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), g⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
      LinearMap.adjoint (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) = (M.rep τ g⁻¹ : M.H τ →ₗ[ℂ] M.H τ) := by
  atlas_forward_decl GlobalTheory.RepAdj.rep_adjoint_eq_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TypeExpand

theorem typeAt_expand : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  intro hU D θ V S M τ _ m k hk B hB φ hφ x g hg
  obtain ⟨H', _, _, σ, lam, ε, P, hen, hds, hPu, hPg, hx⟩ := hφ
  obtain ⟨v, -, ℓ, -, -, hsum⟩ := hx x
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hen
  subst hl he
  obtain ⟨U, hU'⟩ := hU _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P
    (M.fr_unit τ) hPu (M.fr_gram τ) hPg _ _ (M.σ τ) σ (M.ds τ) hds

  set A : ℕ → (M.H τ →ₗ[ℂ] M.H τ) := fun i =>
    ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (U (v i)) with hA
  have key : ∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      ℓ i (σ (P * h * P⁻¹) (v i)) =
        LinearMap.trace ℂ (M.H τ) ((M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) := by
    intro i h hh
    have e1 : (M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i =
        ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (M.rep τ h (U (v i))) := by
      ext w
      simp [hA]
    rw [e1, LinearMap.trace_smulRight]
    have e2 : M.rep τ h (U (v i)) = U (σ (P * h * P⁻¹) (v i)) := (hU' h hh (v i)).symm
    rw [e2]
    simp
  have h1 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
      (∑ j, φ (x * atTau θ V τ (k j)) *
        LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) := by
    refine hasSum_sum fun j _ => ?_
    refine HasSum.mul_right _ ?_
    have := hsum (k j) (hk j)
    refine this.congr_fun ?_
    intro i
    exact (key i (k j) (hk j)).symm
  have h2 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) (φ (x * atTau θ V τ g)) := by
    refine (hsum g hg).congr_fun ?_
    intro i
    rw [key i g hg, hB (A i) g hg]
  exact h2.unique h1

end GlobalTheory.TypeExpand

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelType_form_expands_along_dualFrame : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  atlas_forward_decl GlobalTheory.TypeExpand.typeAt_expand
end

section
section
namespace GlobalTheory

theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  atlas_forward_decl GlobalTheory.expand_pi_of_expand_each
end

section
section
open Finset

namespace GlobalTheory

theorem sum_update_fiber_count {ι : Type} [Fintype ι] [DecidableEq ι] {m : ι → ℕ} (i₀ : ι)
    (G : (∀ i, Fin (m i)) → ℂ) :
    ∑ J : (∀ i, Fin (m i)), ∑ j : Fin (m i₀), G (Function.update J i₀ j) = (m i₀ : ℂ) * ∑ J, G J := by
  let e : (∀ i, Fin (m i)) × Fin (m i₀) ≃ (∀ i, Fin (m i)) × Fin (m i₀) :=
    { toFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p => (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Fintype.sum_prod_type' (fun J j => G (Function.update J i₀ j))]
  rw [Fintype.sum_equiv e (fun p => G (Function.update p.1 i₀ p.2)) (fun p => G p.1) (fun p => rfl)]
  rw [Fintype.sum_prod_type' (fun J (_ : Fin (m i₀)) => G J)]
  simp [Finset.mul_sum]

theorem sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  intro ι _ _ X W _ _ m k ℓ i₀ F F' w w' hone v
  have key : ∀ (u : W i₀) (H : (∀ i, X i) → ℂ) (J : ∀ i, Fin (m i)),
      ∑ j, (∏ i, ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)) *
          H (fun i => k i (Function.update J i₀ j i))
        = (∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i)) *
          ∑ j, ℓ i₀ j u * H (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) := by
    intro u H J
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    have hrest : ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (Function.update J i₀ j i) (Function.update v i₀ u i)
        = ∏ i ∈ ({i₀}ᶜ : Finset ι), ℓ i (J i) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ i₀ := by simpa using hi
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hk : (fun i => k i (Function.update J i₀ j i)) = Function.update (fun i => k i (J i)) i₀ (k i₀ j) := by
      funext i
      exact Function.apply_update k J i₀ j i
    rw [hrest, hk, Function.update_self, Function.update_self]
    ring
  by_cases hm : m i₀ = 0
  · haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by
      have h := J i₀
      rw [hm] at h
      exact h.elim0⟩
    simp
  · have hm' : (m i₀ : ℂ) ≠ 0 := by exact_mod_cast hm
    apply mul_left_cancel₀ hm'
    rw [← sum_update_fiber_count, ← sum_update_fiber_count]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [key w' F J, key w F' J, hone J]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_update_regroup_of_update_eq : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by
  atlas_forward_decl GlobalTheory.sum_prod_update_regroup
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

theorem cusp_decomp : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  intro hP D θ N hθ hs hd φ hφ
  obtain ⟨hAut, -, hType⟩ := hφ
  haveI hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have hmulK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      g * h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun τ g hg h hh => GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh
  have hρ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      (N.M.rep τ (g * h) : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) := by
    intro τ g hg h hh
    rw [rep_mul N.M τ hg hh]
    rfl
  have hframe : ∀ τ, ∃ (m : ℕ) (k : Fin m → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (B : Fin m → (N.M.H τ →ₗ[ℂ] N.M.H τ)), (∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) ∧
      (∀ A : N.M.H τ →ₗ[ℂ] N.M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) =
          ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) *
            LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ
          (B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ))) • B j) :=
    fun τ => GlobalTheory.T.exists_dual_frame_span_unitary_representation (Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) (fun g => (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ))
      (hmulK τ) (hρ τ) (fun g hg => ⟨g⁻¹, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).1, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).2⟩)
  choose m k B hk hB1 hB2 using hframe
  have hexp : ∀ τ x, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), φ (x * atTau θ N.V τ g) =
      ∑ j, φ (x * atTau θ N.V τ (k τ j)) *
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) :=
    fun τ x g hg => GlobalTheory.T.modelType_form_expands_along_dualFrame hP.discreteSeriesHermitianUnique θ N.M τ (k τ) (hk τ) (B τ) (hB1 τ) (hType τ) x hg

  let F : GA D N.V → (D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) → ℂ :=
    fun x g => φ (x * realProd θ N.V g)
  have hsplit : ∀ x (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → ∀ τ₀ g', g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀) →
      F x (Function.update g τ₀ g') = φ ((x * realProd θ N.V (Function.update g τ₀ 1)) * atTau θ N.V τ₀ g') := by
    intro x g hg τ₀ g' hg'
    show φ (x * realProd θ N.V (Function.update g τ₀ g')) = _
    rw [realProd_update hθ hg τ₀ hg', (realProd_commute hθ hg τ₀ hg').eq, mul_assoc]
  have hFexp : ∀ x τ₀ (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → F x g = ∑ j, F x (Function.update g τ₀ (k τ₀ j)) *
        LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ (g τ₀) : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
    intro x τ₀ g hg
    have e0 : F x g = F x (Function.update g τ₀ (g τ₀)) := by rw [Function.update_eq_self]
    rw [e0, hsplit x g hg τ₀ _ (hg τ₀), hexp τ₀ _ _ (hg τ₀)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsplit x g hg τ₀ _ (hk τ₀ j)]

  let bH : ∀ τ, Module.Basis (Fin (Module.finrank ℂ (N.M.H τ))) ℂ (N.M.H τ) := fun τ => Module.finBasis ℂ (N.M.H τ)
  let ℓ : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → ∀ τ, Fin (m τ) → (N.M.sm τ →ₗ[ℂ] ℂ) :=
    fun a τ j => (bH τ).coord (a τ) ∘ₗ B τ j ∘ₗ (N.M.sm τ).subtype
  let T : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → MMap N.M := fun a =>
    ∑ J : (∀ τ, Fin (m τ)), ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap
      (fun τ => ℓ a τ (J τ))).smulRight (fun x => F x (fun τ => k τ (J τ)))
  have hT : ∀ a v x, T a v x = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) * F x (fun τ => k τ (J τ)) := by
    intro a v x
    simp only [T, MultilinearMap.sum_apply, Finset.sum_apply, MultilinearMap.smulRight_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Pi.smul_apply, smul_eq_mul]
  have hMult : ∀ a, IsMultMap θ N.M ∅ 1 (T a) := by
    intro a
    refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _,
      fun v k' hk' => absurd hk' (Set.notMem_empty k'), fun τ₀ h hh v w hw => ?_, fun τ v x => ?_⟩
    · have e : T a v = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) •
          rTr N.V (realProd θ N.V (fun τ => k τ (J τ))) φ := by
        funext x
        rw [hT, Finset.sum_apply]
        rfl
      rw [e]
      refine Finset.sum_induction _ (IsAutFunSm θ N.V) (fun f g hf hg => GlobalTheory.MultMem.isAutFunSm_add hf hg) ?_
        (fun J _ => GlobalTheory.MultMem.isAutFunSm_smul _ (isAutFunSm_realProd hθ _ hAut))
      exact Formalism.L2.Theta.isAutFunSm_const (θ := θ) (V := N.V) (c := (0 : ℂ))
    · funext x
      have hkJ : ∀ J : (∀ τ, Fin (m τ)), ∀ τ, (fun τ => k τ (J τ)) τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
        fun J τ => hk τ (J τ)
      have hF' : ∀ J : (∀ τ, Fin (m τ)), F (x * atTau θ N.V τ₀ h) (fun τ => k τ (J τ)) =
          F x (Function.update (fun τ => k τ (J τ)) τ₀ (h * k τ₀ (J τ₀))) := by
        intro J
        show φ (x * atTau θ N.V τ₀ h * realProd θ N.V _) = φ (x * realProd θ N.V _)
        have e1 := realProd_update hθ (hkJ J) τ₀ (hmulK τ₀ h hh _ (hk τ₀ (J τ₀)))
        have e2 := realProd_update hθ (hkJ J) τ₀ (hk τ₀ (J τ₀))
        rw [Function.update_eq_self] at e2
        rw [e1, e2, GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ₀ hh (hk τ₀ (J τ₀))]
        simp only [mul_assoc]
      show T a (Function.update v τ₀ w) x = T a v (x * atTau θ N.V τ₀ h)
      rw [hT, hT]
      simp only [hF']
      have key := GlobalTheory.T.sum_prod_update_regroup_of_update_eq (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) (W := fun τ => N.M.sm τ)
        k (ℓ a) τ₀ (F x) (fun g => F x (Function.update g τ₀ (h * g τ₀))) (v τ₀) w ?_ v
      · rw [Function.update_eq_self] at key
        exact key
      intro J
      simp only [Function.update_idem, Function.update_self]
      have hf : ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀), F x (Function.update (fun τ => k τ (J τ)) τ₀ g') =
          ∑ j, F x (Function.update (fun τ => k τ (J τ)) τ₀ (k τ₀ j)) *
            LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ g' : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
        intro g' hg'
        rw [hsplit x _ (hkJ J) τ₀ g' hg', hexp τ₀ _ g' hg']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsplit x _ (hkJ J) τ₀ _ (hk τ₀ j)]
      have := equiv_one (Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀)) (fun g => (N.M.rep τ₀ g : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀))
        (hρ τ₀) (k τ₀) (hk τ₀) (B τ₀) (hB2 τ₀) _ hf (hmulK τ₀) ((bH τ₀).coord (a τ₀)) (v τ₀ : N.M.H τ₀) hh
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, hw]
      exact this
    · exact GlobalTheory.DefiniteEnd.exists_sobCont N.M τ (T a) v x
  have hmem : ∀ a, PiTensorProduct.lift (T a) ∈ N.Cusp θ := fun a =>
    (mem_multT θ N.M ∅ 1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact Submodule.subset_span (hMult a))
  let e : ∀ τ, Fin (Module.finrank ℂ (N.M.H τ)) → N.M.sm τ := fun τ i => ⟨bH τ i, by rw [sm_eq_top N.M τ]; trivial⟩
  have htr : ∀ τ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ 1 : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) =
      ∑ i, (bH τ).coord i (B τ j (bH τ i)) := by
    intro τ j
    rw [rep_one N.M τ, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.trace_eq_matrix_trace ℂ (bH τ), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  have hrep : ∀ x, φ x = ∑ a : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))), T a (fun τ => e τ (a τ)) x := by
    intro x
    have h1 : φ x = F x (fun _ => 1) := by
      show φ x = φ (x * realProd θ N.V _)
      rw [realProd_one hθ, mul_one]
    have h2 := GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (fun τ => Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) m k hk
      (fun τ j g => LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j)) (F x)
      (fun τ₀ g hg => hFexp x τ₀ g hg) (fun _ => 1) (fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _)
    rw [h1, h2]
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [htr]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  let eqv := Fintype.equivFin (∀ τ, Fin (Module.finrank ℂ (N.M.H τ)))
  refine ⟨Fintype.card _, fun i => ⟨PiTensorProduct.lift (T (eqv.symm i)), hmem _⟩,
    fun i => PiTensorProduct.tprod ℂ (fun τ => e τ (eqv.symm i τ)), ?_⟩
  funext x
  rw [hrep x, Finset.sum_apply]
  simp only [PiTensorProduct.lift.tprod]
  exact (Equiv.sum_comp eqv.symm (fun a => T a (fun τ => e τ (a τ)) x)).symm

end GlobalTheory.DefiniteDecomp
end
end
