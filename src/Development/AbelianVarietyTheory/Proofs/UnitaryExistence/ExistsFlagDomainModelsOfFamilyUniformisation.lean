import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOfFinOrderOfBounded
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem princ_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ _
  haveI := Di.fin
  have hΛ : (LinearMap.range φ0).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map φ0 Module.Finite.fg_top
  have hM : 0 < l.M * l.A := Nat.mul_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨S, hS⟩ := GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM
  refine ⟨S, fun γ hγ => ?_⟩
  obtain ⟨s, hs, hst, hc⟩ := hS γ hγ
  refine ⟨s, hs, hst, fun a _ => ?_, fun a => ?_⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.A • b, by rw [e, map_nsmul, mul_smul]⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.M • b, by rw [e, map_nsmul, mul_comm, mul_smul]⟩

end GlobalTheory.FrameUnif
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  atlas_forward_decl GlobalTheory.FrameUnif.princ_finiteIndex
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincFree

theorem cmType_of_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hE]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : z.re = 0 := by
      by_contra h
      have h4 : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [h4] at h1
      nlinarith [mul_self_nonneg z.re]
    apply Complex.ext <;> simp [h3]
  have hne : H.rt0 ≠ 0 := by
    intro h
    have h1 := H.sqrt_neg_disc_sq
    rw [h] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  rw [ComplexEmbedding.conjugate_coe_eq, hconj _ hsq]
  constructor
  · intro h h'
    rw [h] at h'
    exact hne (by linear_combination (-1 / 2 : ℂ) * h')
  · intro h
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [hsq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    {r : ℕ} (φ : L →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ LinearMap.range φ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ LinearMap.range φ) :
    ∃ g : L ≃ₗ[𝓞 E] L, ∀ a, φ (g a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)
  let g : L →ₗ[𝓞 E] L :=
    { toFun := f
      map_add' := fun a b => hφ (by rw [map_add, hf, hf, hf, map_add, Matrix.mulVec_add])
      map_smul' := fun c a => hφ (by
        rw [RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩
  · have h : f a = f b := hab
    rw [← hli (φ a), ← hli (φ b), ← hf, ← hf, h]
  · obtain ⟨a, ha⟩ := (hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2
      (by rw [hri]; exact LinearMap.mem_range_self φ b)
    exact ⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩

theorem princ_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb
  obtain ⟨hU, hhalf, -⟩ := hγ
  obtain ⟨g, hg⟩ := exists_equiv_of_stab φ0 hinj γ hU.2
  have hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a' := by
    intro a a'
    have : ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ) := by
      rw [hEF, hEF, hg, hg, hU.1]
    exact_mod_cast this
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by
    obtain ⟨e, he⟩ := hhalf a ha
    exact ⟨e, hinj (by rw [hg, he, map_add, map_nsmul])⟩)
  have hfin := Di.fin
  refine GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ
    (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb
  · rw [hΨ, hΨ]; exact cmType_of_rt H τ
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ0
  · rw [LinearMap.coe_range]; exact hsp
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add, map_nsmul]⟩

end GlobalTheory.PrincFree
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalGroup_acts_freely_on_flags : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  atlas_forward_decl GlobalTheory.PrincFree.princ_free
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincTransv

theorem transv_mem_princ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 hξ h
  have hξ' : IsCMField.complexConj E ξ₀ = -ξ₀ := hξ
  have hG := h.2.2.1
  have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H Di r (-ξ₀) Gm φ0
    (by simp [cc, hξ']) h).2.2.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  set d : ℕ := (NumberField.discr E).natAbs with hd
  have hd0 : 0 < d := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  refine ⟨l.M * l.A * d, Nat.mul_pos (Nat.mul_pos hM l.A_pos) hd0, ?_⟩
  intro κ0 hκ ξ hξΛ hiso s hs hsi
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have hs' : IsCMField.complexConj E s = s := hs
  set α : E := ((l.M * l.A * d : ℕ) : E) * s * κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hs', hκc]
  have h2 : IsIntegral ℤ (2 : E) := isIntegral_natCast 2
  have hint' : ∀ v ∈ LinearMap.range φ0, IsIntegral ℤ ((d : E) * κ0 * herm Gm v ξ) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hξΛ
    have h1 := h2.mul (hint x y)
    have hdd : (d : E) = (NumberField.discr E : E) ∨ (d : E) = -(NumberField.discr E : E) := by
      rcases Int.natAbs_eq (NumberField.discr E) with h | h
      · left; rw [h, Int.cast_natCast]
      · right; rw [h, Int.cast_neg, Int.cast_natCast, neg_neg]
    have hpm : (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))) ∨
        (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          -(2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y)))) := by
      rcases hdd with e | e <;> rcases hκ with e' | e' <;> rw [e, e']
      · right; ring
      · left; ring
      · left; ring
      · right; ring
    rcases hpm with e | e <;> rw [e]
    · exact h1
    · exact h1.neg
  have key : ∀ v ∈ LinearMap.range φ0,
      (s * ((d : E) * κ0 * herm Gm v ξ)) • ξ ∈ LinearMap.range φ0 := fun v hv =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hsi.mul (hint' v hv)) hξΛ
  have e : ∀ v, (α * herm Gm v ξ) • ξ =
      (l.M * l.A) • ((s * ((d : E) * κ0 * herm Gm v ξ)) • ξ) := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  refine ⟨GlobalTheory.FlagData.transv Gm hiso α, ⟨⟨GlobalTheory.FlagData.herm_transvMat hG hiso hα, fun x => ?_⟩,
    fun a _ => ?_, fun a => ?_⟩, rfl⟩
  · change x ∈ LinearMap.range φ0 ↔ transvMat Gm ξ α *ᵥ x ∈ LinearMap.range φ0
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (by rw [e]; exact nsmul_mem (key x hx) _), fun hx => ?_⟩
    have h := nsmul_mem (key _ hx) (l.M * l.A)
    rw [← e, GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.A • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_smul]
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.M • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_comm, mul_smul]

end GlobalTheory.PrincTransv
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvection_mem_principalCongruenceGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  atlas_forward_decl GlobalTheory.PrincTransv.transv_mem_princ
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_den_herm_model (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
      IsIntegral ℤ ((den : E) * herm Gm x y) := by
  by_cases hξ0 : ξ = 0
  · have hz : ∀ z : D.La, z = 0 := fun z => by
      apply D.unimod.1
      ext y
      have := h.2.2.2.2 z y
      rw [hξ0, zero_mul, map_zero] at this
      simpa using this
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hz y, map_zero, GlobalTheory.HermModel.herm_zero_right, mul_zero]
    exact isIntegral_zero
  · have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ h).2.2.1
    have halg : IsAlgebraic ℤ ξ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic ξ)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hd : IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ)) :=
      (isIntegral_algebraMap (R := ℤ) (A := E) (x := NumberField.discr E)).mul hn
    refine ⟨⟨_, hd⟩, ?_, ?_⟩
    · intro h0
      have h1 : (NumberField.discr E : E) * (n • ξ) = 0 := congrArg Subtype.val h0
      rw [zsmul_eq_mul] at h1
      exact mul_ne_zero (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
        (mul_ne_zero (Int.cast_ne_zero.2 hn0) hξ0) h1
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h2 := (isIntegral_algebraMap (R := ℤ) (A := E) (x := n)).mul (hint x y)
      have e : (NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y) =
          algebraMap ℤ E n * ((NumberField.discr E : E) * (ξ * herm Gm (φ x) (φ y))) := by
        rw [zsmul_eq_mul, eq_intCast]; ring
      change IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y))
      rw [e]; exact h2

theorem latModel_of_same_signature : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw Di : Datum H) (r : ℕ) (Ψ : Finset (E →+* ℂ)) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), Di.p = Dw.p → Di.q = Dw.q → (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → cc ξ₀ = -ξ₀ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → LatModel l Ψ Gm ξ₀ Dw.q Di := by
  intro hN E _ _ _ H l Dw Di r Ψ ξ₀ Gm φ hp hq hΨ hξ h
  have hξ' : cc (-ξ₀) = -(-ξ₀) := by
    have : cc (-ξ₀) = -cc ξ₀ := by simp [cc]
    rw [this, hξ]
  obtain ⟨φ0, h0⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hN) hN
    E H Dw Di r (-ξ₀) Gm φ hp hq hξ' h
  refine ⟨φ0, h0.1, h0.2.2.2.2, ?_, exists_den_herm_model E H Di r (-ξ₀) Gm φ0 hξ' h0,
    GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser E H l Di r ξ₀ Gm φ0 hξ h0, GlobalTheory.T.principalGroup_acts_freely_on_flags E H l Di r ξ₀ Gm φ0 hξ h0 Ψ Dw.q hΨ,
    GlobalTheory.T.transvection_mem_principalCongruenceGroup E H l Di r ξ₀ Gm φ0 hξ h0⟩
  rw [LinearMap.coe_range]; exact h0.2.1

end GlobalTheory.FrameUnif
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeModel_of_same_signature_hasseNorm : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw Di : Datum H) (r : ℕ) (Ψ : Finset (E →+* ℂ)) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), Di.p = Dw.p → Di.q = Dw.q → (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → cc ξ₀ = -ξ₀ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → LatModel l Ψ Gm ξ₀ Dw.q Di := by
  atlas_forward_decl GlobalTheory.FrameUnif.latModel_of_same_signature
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ModelsExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {r : ℕ}

theorem rt0_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have h2 : (H.d : ℂ) = 0 := by simpa using h1
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem rt0_conj_neg_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h1 : (starRingEnd ℂ H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exfalso
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp [pow_two, him] at h2
    nlinarith [mul_self_nonneg H.rt0.re]
  · exact h

theorem emb_rt_eq_or (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  have h : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [← map_pow, h, H.sqrt_neg_disc_sq]; simp

theorem cm_type (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hne : -H.rt0 ≠ H.rt0 := fun h => rt0_ne_zero H (by linear_combination (-1 / 2 : ℂ) * h)
  rcases emb_rt_eq_or H τ with h | h
  · rw [h, rt0_conj_neg_ne_zero]; simp [hne]
  · rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]; simp [hne]

theorem exists_emb (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0
  · exact ⟨_, h⟩
  · exact ⟨τ, (cm_type H τ).2 h⟩

def dataOf (l : Level H) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (ξ₀ : E) (q : ℕ)
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (hherm : ∀ a b, cc (Gm a b) = Gm b a) (hdet : Gm.det ≠ 0) (hq : q ≤ r)
    (hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ))
    (hξ : cc ξ₀ = -ξ₀) (hξ0 : ξ₀ ≠ 0) (hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0)
    (Di : Datum H) (hL : LatModel l Ψ Gm ξ₀ q Di) : Data E r where
  Ψ := Ψ
  cmType := hΨ
  Gm := Gm
  Gm_herm := hherm
  Gm_det := hdet
  p0 := q
  p0_le := hq
  signature := hsig
  Λ := LinearMap.range hL.choose
  Λ_fg := by
    have := Di.fin
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  Λ_span := hL.choose_spec.2.2.1
  den := hL.choose_spec.2.2.2.1.choose
  den_ne := hL.choose_spec.2.2.2.1.choose_spec.1
  Λ_int := hL.choose_spec.2.2.2.1.choose_spec.2
  Γ := GlobalTheory.FrameUnif.princ l Gm Di hL.choose
  Γ_stab := fun _ hγ => hγ.1
  Γ_index := hL.choose_spec.2.2.2.2.1
  Γ_free := hL.choose_spec.2.2.2.2.2.1
  χ := fun _ _ => 1
  χ_mul := fun _ _ _ _ _ => (mul_one 1).symm
  χ_add := fun _ _ _ _ => (mul_one 1).symm
  χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩
  ξ0 := ξ₀
  ξ0_im := hξ
  ξ0_ne := hξ0
  κ0 := 2 * ξ₀
  κ0_xi := Or.inl rfl
  κ0_sign := hκ
  m := hL.choose_spec.2.2.2.2.2.2.choose
  m_pos := hL.choose_spec.2.2.2.2.2.2.choose_spec.1
  transv := fun ξ hξ h0 s hs hsi =>
    hL.choose_spec.2.2.2.2.2.2.choose_spec.2 _ (Or.inl rfl) ξ hξ h0 s hs hsi

theorem exists_modelsOf : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ M : ModelsOf F r, ModelBase M ∧ NegXi M ∧ ∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀ := by
  classical
  intro hN E _ _ _ H Dw l Xo σ' g ty F r ξ₀ Gm φ hξ hneg hφ
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hmem : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  have hξ' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hξ ⊢
    rw [map_neg, hξ]
  have hrk : r = Dw.p + Dw.q := (GlobalTheory.HermModel.rank_integral_selfDual E H Dw r (-ξ₀) Gm φ hξ' hφ).1
  have hq : Dw.q ≤ r := by omega
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := fun τ => by
    rw [hmem, hmem]; exact cm_type H τ
  have hsig : ∀ τ : Ψ, ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      gram τ.1 Gm P = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ) := fun τ => by
    have hτ := (hmem τ.1).1 τ.2
    refine (GlobalTheory.T.signature_hermitian_model_of_datum E H Dw r (-ξ₀) Gm φ hξ' hφ τ.1 hτ).1 ?_
    have := hneg τ.1 hτ
    rw [map_neg, Complex.neg_im]
    linarith
  have hξ0 : ξ₀ ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := exists_emb H
    simpa using hneg τ hτ
  have hκ : ∀ τ : Ψ, (τ.1 (2 * ξ₀)).im < 0 := fun τ => by
    have := hneg τ.1 ((hmem τ.1).1 τ.2)
    rw [two_mul, map_add, Complex.add_im]
    linarith
  have hL : ∀ i, LatModel l Ψ Gm ξ₀ Dw.q (F.Di i) := fun i =>
    GlobalTheory.T.latticeModel_of_same_signature_hasseNorm hN E H l Dw (F.Di i) r Ψ ξ₀ Gm φ (F.sig i).1 (F.sig i).2 hmem hξ hφ
  refine ⟨⟨fun i => dataOf l Ψ Gm ξ₀ Dw.q hΨ hφ.2.2.1 hφ.2.2.2.1 hq hsig hξ hξ0 hκ (F.Di i) (hL i),
    fun i => LinearEquiv.ofInjective (hL i).choose (hL i).choose_spec.1⟩, ?_,
    fun k τ hτ => hneg τ ((hmem τ).1 hτ), fun k => ⟨rfl, rfl⟩⟩
  exact
    { rank := hrk
      type := fun k => ⟨rfl, hmem⟩
      chi := fun _ _ _ => rfl
      ef := fun k a b => (hL k).choose_spec.2.1 a b
      gam := fun k γ => Iff.rfl
      domStab := fun k x hx => ⟨fun b hb => dom_rmul _ hx hb, fun γ hγ => dom_lact _ hx hγ.1⟩ }

end GlobalTheory.ModelsExist
end
end
