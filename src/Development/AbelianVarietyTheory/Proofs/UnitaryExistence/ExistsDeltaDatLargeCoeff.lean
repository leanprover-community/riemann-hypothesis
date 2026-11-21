import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.SplitPrimeData

theorem exists_char_ne_one {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) [Finite (R ⧸ I)]
    {r : ℕ} (hr : 1 ≤ r) (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (h2 : (-1 : (R ⧸ I)ˣ) ≠ 1) :
    ∃ ψ : (Q ≃ₗ[R] Q) →* ℂˣ, ψ ≠ 1 := by
  classical
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs) (fun a b => by
      ext x i
      simp [LinearEquiv.mul_apply])
  let i₀ : Fin r := ⟨0, hr⟩
  let δ : Fin r → R ⧸ I := Function.update 1 i₀ (-1)
  have hδ : Matrix.diagonal δ * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = i₀
    · subst h; simp [δ]
    · simp [δ, h]
  let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) := Matrix.toLin'OfInv hδ hδ
  have hg : LinearEquiv.det g = -1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) = Matrix.toLin' (Matrix.diagonal δ) := rfl
    rw [this, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
    ext x i
    simp [cj]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (R ⧸ I)ˣ ℂ h2
  refine ⟨φ.comp (LinearEquiv.det.comp cj), fun h => hφ ?_⟩
  have := DFunLike.congr_fun h (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm)
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, hk, hg] at this

theorem value_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hm : ζ ∈ c.F) (f : Rul Xo c) (hf : f ^ N = 1) (y : FrPt Xo c (CAt c.F.val.toRingHom))
    (h0 : evR Xo c f y ≠ 0) : ∃ a : c.F, evR Xo c f y = algebraMap c.F (CAt c.F.val.toRingHom) a := by
  have : IsDomain (CAt c.F.val.toRingHom) := inferInstanceAs (IsDomain ℂ)
  have hmul : ∀ a b : Rul Xo c, evR Xo c (a * b) y = evR Xo c a y * evR Xo c b y :=
    fun a b => evalAt_mul _ _ a b y
  have e₁ : evR Xo c 1 y = 1 := by
    have := hmul f 1
    rw [mul_one] at this
    exact (mul_eq_left₀ h0).1 this.symm
  have e₂ : ∀ m : ℕ, evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, e₁]
    | succ m ih => rw [pow_succ, pow_succ, hmul, ih]
  have e₃ := e₂ N
  rw [hf, e₁] at e₃
  have : NeZero N := ⟨hN.ne'⟩
  let z : ℂ := evR Xo c f (S := CAt c.F.val.toRingHom) y
  have e₄ : z ^ N = 1 := e₃.symm
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one e₄
  exact ⟨⟨ζ ^ i, pow_mem hm i⟩, hi.symm⟩


end GlobalTheory.SplitPrimeData
