import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitCentreDerivativeCommuteCentralEigen

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idelic_absValue_cpow_character : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  first | exact @GlobalTheory.ResW.exists_abs_cpow | exact GlobalTheory.ResW.exists_abs_cpow | (intros; apply GlobalTheory.ResW.exists_abs_cpow <;> assumption)
end

section
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.Published

namespace GlobalTheory.CuspSchur

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def imgPart (π : CuspSub E a) (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (w : W) : Submodule ℂ π.V where
  carrier := {ψ | (∀ k ∈ L, π.op (.fin k) ψ = ψ) ∧
    ∃ T : W →ₗ[ℂ] π.V, (∀ k v, T (ρ k v) = π.op (.cpt k) (T v)) ∧ T w = ψ}
  add_mem' := by
    rintro x y ⟨h1, T, h2, rfl⟩ ⟨h3, T', h4, rfl⟩
    exact ⟨fun k hk => by rw [map_add, h1 k hk, h3 k hk], T + T', fun k v => by simp [h2, h4], rfl⟩
  zero_mem' := ⟨fun _ _ => map_zero _, 0, fun _ _ => by simp, rfl⟩
  smul_mem' := by
    rintro c x ⟨h1, T, h2, rfl⟩
    exact ⟨fun k hk => by rw [map_smul, h1 k hk], c • T, fun k v => by simp [h2], rfl⟩

theorem finiteDimensional_imgPart (π : CuspSub E a) {L : Subgroup (GL (Fin a) (Af E))}
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (Kinf E a) W} (hρ : AutFin.IsContRep ρ) (w : W) :
    FiniteDimensional ℂ (imgPart π L ρ w) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := GlobalTheory.automorphicFormsFiniteGL E a L hL W ρ hρ c
  refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ (imgPart π L ρ w).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms L ρ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => congrArg Subtype.val (v.2.1 k hk), fun g => ?_,
      fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  obtain ⟨T, hT, e⟩ := v.2.2
  have h := AutFinGL.type_of_map ρ (π.V.subtype ∘ₗ T) (fun k w => congrArg Subtype.val (hT k w)) w g
  rw [LinearMap.comp_apply, e] at h
  exact h

theorem schur : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (x : CuspSub E a)
    (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  intro E _ _ _ a π f hf
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hL : IsOpen (LocEx.stab π.finPart ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  have : FiniteDimensional ℂ (LocEx.orbSpan φ) := (π.cusp φ hφ).1.kfin
  have hSV : LocEx.orbSpan φ ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact π.stable (.cpt k) φ hφ)
  let w : LocEx.orbSpan φ := ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩
  let U := imgPart π (LocEx.stab π.finPart ⟨φ, hφ⟩) (sub (cptRep E a) _ (LocEx.orbSpan_stable φ)) w
  have : FiniteDimensional ℂ U := finiteDimensional_imgPart π hL (LocEx.isContRep_sub _ _) w
  have hφU : (⟨φ, hφ⟩ : π.V) ∈ U := ⟨fun k hk => hk, Submodule.inclusion hSV, fun _ _ => rfl, rfl⟩
  have hfU : ∀ v ∈ U, f v ∈ U := by
    rintro _ ⟨h1, T, h2, rfl⟩
    exact ⟨fun k hk => by rw [← hf, h1 k hk], f ∘ₗ T, fun k v => by simp [h2, hf], rfl⟩
  have : Nontrivial U := ⟨⟨⟨_, hφU⟩, 0, fun e => h0 (congrArg (fun z : U => z.1.1) e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict hfU)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hv1 : f v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases π.irred ((Module.End.eigenspace f c).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨y, hy, rfl⟩
    refine ⟨π.op o y, Module.End.mem_eigenspace_iff.2 ?_, rfl⟩
    rw [hf, Module.End.mem_eigenspace_iff.1 hy, map_smul]) with h1 | h1
  · have h2 : v.1.1 ∈ (Module.End.eigenspace f c).map π.V.subtype := ⟨v.1, Module.End.mem_eigenspace_iff.2 hv1, rfl⟩
    rw [h1] at h2
    exact absurd (Subtype.ext (Subtype.ext ((Submodule.mem_bot ℂ).1 h2))) hv.2
  · intro ψ
    obtain ⟨y, hy, e⟩ : ψ.1 ∈ (Module.End.eigenspace f c).map π.V.subtype := h1.symm ▸ ψ.2
    obtain rfl : y = ψ := Subtype.ext e
    exact Module.End.mem_eigenspace_iff.1 hy

end GlobalTheory.CuspSchur

end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (x : CuspSub E a) (f : x.V →ₗ[ℂ] x.V), (∀ o φ, f (x.op o φ) = x.op o (f φ)) → ∃ c : ℂ, ∀ φ, f φ = c • φ := by
  atlas_forward_decl GlobalTheory.CuspSchur.schur
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCentreDerivative_commute_central_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), (∀ o : Op E N, zc E N * act o = act o * zc E N) ∧ zc E N ∈ Zalg E N ∧ ∀ (φ : Sm E N) (c : ℂ), zc E N φ = c • φ ↔ ∀ (t : ℝ) (g : GA E N), φ.1 (splitCentre E N t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.ResW.zc_comm_mem_eigen | exact GlobalTheory.ResW.zc_comm_mem_eigen | (intros; apply GlobalTheory.ResW.zc_comm_mem_eigen <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.CexLetter

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem zc_eq_act (a : ℕ) : zc E a = act (Op.lie (fun i j => if i = j then 1 else 0) : Op E a) := rfl

theorem zc_mapsTo {a : ℕ} (π : CuspSub E a) : ∀ φ ∈ π.V, zc E a φ ∈ π.V := fun φ hφ => by
  rw [zc_eq_act]; exact π.stable _ φ hφ

theorem exists_scalar (x : Letter E) : ∃ c : ℂ, ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.cuspidalRep_endomorphism_scalar_schur E x.1 x.2 ((zc E x.1).restrict (zc_mapsTo x.2)) (by
    intro o φ
    apply Subtype.ext
    have := congrArg (fun f : Module.End ℂ (Sm E x.1) => f φ.1) ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).1 o)
    simpa [LinearMap.restrict_apply, CuspSub.op] using this)
  exact ⟨c, fun φ hφ => by simpa using congrArg Subtype.val (hc ⟨φ, hφ⟩)⟩

theorem cex_spec (x : Letter E) : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ := by
  unfold cex; exact Classical.epsilon_spec (exists_scalar x)

theorem cex_unique (x : Letter E) (c : ℂ) (h : ∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) : cex x = c := by
  obtain ⟨φ, hφ, hne, hc⟩ := h
  have h1 := cex_spec x φ hφ
  rw [hc] at h1
  exact (smul_left_injective ℂ hne h1).symm

theorem cex_tw (x : Letter E) (t : ℝ) : cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t := by
  obtain ⟨χ, h1, -, -, h4⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (t : ℂ)
  have hχ : χ = nu E t := by have := h4 (Complex.ofReal_im t); rwa [Complex.ofReal_re] at this
  subst hχ
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
  apply cex_unique
  refine ⟨mulChi x.1 (nu E t) φ, ?_, ?_, ?_⟩
  · exact ⟨φ, hφ, rfl⟩
  · exact fun h0 => hne ((mulChi x.1 (nu E t)).injective (h0.trans (map_zero _).symm))
  · show zc E x.1 (mulChi x.1 (nu E t) φ) = _
    rw [h1, cex_spec x φ hφ, ← add_smul, map_smul]
    rfl

theorem rexp_tw (x : Letter E) (hx : 1 ≤ x.1) (t : ℝ) : rexp (tw x t) = rexp x + t := by
  have hd : (0:ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha : (0:ℝ) < x.1 := by exact_mod_cast hx
  have hne : (x.1 : ℝ) * Module.finrank ℚ E ≠ 0 := (mul_pos ha hd).ne'
  unfold rexp
  rw [cex_tw]
  show (cex x + (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ)).re / ((x.1:ℝ) * Module.finrank ℚ E) = _
  rw [show (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ) = (((x.1:ℝ) * Module.finrank ℚ E * t : ℝ) : ℂ) by
    push_cast; ring, Complex.add_re, Complex.ofReal_re]
  field_simp

theorem cex_eq_zero_iff (x : Letter E) : cex x = 0 ↔ IsNormalised x.2 := by
  constructor
  · intro h φ hφ t g
    have := ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).1 (by rw [← h]; exact cex_spec x φ hφ) t g
    simpa using this
  · intro hN
    obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
    exact cex_unique x 0 ⟨φ, hφ, hne, ((GlobalTheory.T.splitCentreDerivative_commute_central_eigen E x.1).2.2 φ 0).2 (fun t g => by simpa using hN φ hφ t g)⟩

end GlobalTheory.ResW.CexLetter

open GlobalTheory.ResW.CexLetter in

theorem GlobalTheory.ResW.letter_centralExponent : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : Letter E), (∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ) ∧ (∀ t : ℝ, cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t) ∧ (1 ≤ x.1 → ∀ t : ℝ, rexp (tw x t) = rexp x + t) ∧ (cex x = 0 ↔ IsNormalised x.2) ∧ ∀ c : ℂ, (∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) → cex x = c := by
  intro E _ _ _ x
  exact ⟨cex_spec x, cex_tw x, rexp_tw x, cex_eq_zero_iff x, fun c h => cex_unique x c h⟩
end
end
