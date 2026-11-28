module

public import Lib.ClassField.HeckeCharacter.AlgebraicValues
import Lib.ClassField.Global.AlbertBrauerHasseNoether
import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.ClassField.HeckeL.ContinuationAtOne

/-!
# Base change of U(1) and algebraic Hecke characters, and their L-functions

Let `E` be a CM field with CM type `Φ`. A character `ν` of `U(1)(𝔸)` trivial on rational points
gives by base change the Hecke character `x ↦ ν(x / x̄)` of `E`. For `e ≠ 0` and `S` finite, its
`L`-function without the factors at `S ∪ S̄` does not vanish at real `s ≥ 1`. Algebraic Hecke
characters are also base changed along the norm.

## Main definitions and results

* `New.AutChar.L`: the Euler product of the base change, without the factors at `S ∪ S̄`.
* `New.AutChar.HasWeight.L_ne_zero`: for `e ≠ 0` and `S` finite, this `L`-function does not vanish
  at real `s ≥ 1`.
* `New.AutChar.HasWeight.toAlgebraic`: the algebraic Hecke character
  `ν(x / x̄) υ(x)^{-k} |x|^{j - k/2}`, with `υ` the splitting character of `New.SplittingChar`.
* `New.AlgHeckeChar.baseChange`: base change `ω ∘ N` of an algebraic Hecke character along the norm.

Notions from other files:
* `New.AutChar`: The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of
  the CM field E, trivial on elements coming from E.
* `New.HeckeChar`: The group of unitary Hecke characters of E: continuous circle-valued characters
  of the idele group trivial on principal ideles.
* `New.IsHeckeOfType`: The character ψ of the finite ideles is the finite part of a Hecke character
  of type n: its kernel is open and ψ(x) ∏_w (Φ_w(x)/|Φ_w(x)|)^{n_w} = 1 on K^×.
* `New.IsHeckeOfType.toAlgebraic`: the algebraic character `ψ |·|^{k/2}` of infinity type `m`, for
  `ψ` of type `m (Φ w) - m (Φ̄ w)` with `m (Φ w) + m (Φ̄ w) = k` at every infinite place `w`.
* `New.AutChar.HasWeight`: μ has weight e and tame part ψ: almost all residue characters ψ_w are
  trivial, and μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part.
* `New.heckeCoeff` φ S: the value of φ at the chosen uniformiser at v for v outside S, and 0 for v
  in S; `New.eulerProd` a is the Euler product ∏_v (1 - a_v q_v^(-s))⁻¹.

## Relation to the literature

Known; see `Lib.ClassField.HeckeL.ContinuationAtOne`,
`Lib.ClassField.Avatar.LocalGlobalCompatibility` and `Lib.ClassField.Global.CMSplittingCharacters`
for sources.
-/

@[expose] public section

noncomputable section

namespace New

/-!
## Base change of U(1) characters: L-function and algebraicity

Conventions: `ν.HasWeight e ψ` says that `ν` has weight `e` at infinity and tame part `ψ` (one
character `ψ w` of each residue field). `star` is complex conjugation, also on places. `χ.finPart`
is the restriction to finite ideles, and `χ.atUniformizer w` is the value at the chosen uniformiser
at `w`.
-/

section AutCharLFunction

open WeilData Finset Complex Real Variety

variable {E : Type _} [Field E] [CMType E] {e : NumberField.InfinitePlace E → ℤ} (ν : AutChar E)

/-- The Euler product of the character `x ↦ ν (x / x̄)` of `E`, without the factors at `S ∪ S̄`.
It is the partial Hecke `L`-function if `S ∪ S̄` contains the ramified places. -/
def AutChar.L (S : Set (FinPlace E)) : ℝ → ℂ :=
  eulerProd (heckeCoeff ν.baseChange.finPart (Set.conjClosure S))

namespace AutChar.HasWeight

variable {ν} {S : Set (FinPlace E)}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} [h : ν.HasWeight e ψ]
  {w : FinPlace E} (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1)

include h

/-- Let `ν` have weight `e`. At an idele `y` with finite part `1`, the Hecke character
`y ↦ ν(y / ȳ) υ(y) ^ (-k)` takes the value `∏ w, (y_w / |y_w|) ^ (2 e_w - k)`. -/
lemma baseChange_mul_upsilon_zpow_inv_apply [WeilData E] (k : ℤ) (y : (𝔸 E)ˣ)
    (hy_fin : (y : 𝔸 E).2 = 1) :
    ((ν.baseChange * (υ ^ k)⁻¹).val y : ℂ) =
      ∏ w : NumberField.InfinitePlace E, ((y : 𝔸 E).1 w / ‖(y : 𝔸 E).1 w‖) ^ (2 * e w - k) := by
  let z : (NumberField.InfinitePlace E → ℂ)ˣ := y.map (MonoidHom.fst _ (𝔸f E))
  have hy : y = z.map (MonoidHom.inl _ (𝔸f E)) := Units.ext (Prod.ext rfl hy_fin)
  let u (w : NumberField.InfinitePlace E) : ℂ := z.val w / ‖z.val w‖
  have hu_ne (w : NumberField.InfinitePlace E) : u w ≠ 0 := by
    simpa [u] using (z.isUnit.apply w).ne_zero
  -- At infinity the base change has type `2 e` and `υ` has type `1`.
  have h_base : (ν.baseChange.val y : ℂ) = ∏ w, u w ^ (2 * e w) := by
    simpa [hy] using h.baseChange_apply_inf z
  have h_upsilon : (υ.val y : ℂ) = ∏ w, u w :=
    υ_unit y (by simp [show y.map (MonoidHom.snd _ (𝔸f E)) = 1 from Units.ext hy_fin])
  calc ((ν.baseChange * (υ ^ k)⁻¹).val y : ℂ)
      = (ν.baseChange.val y : ℂ) / (υ.val y : ℂ) ^ k := by
        cases k <;> simp [div_eq_mul_inv]
    _ = ∏ w, u w ^ (2 * e w) / u w ^ k := by
        rw [h_base, h_upsilon, ← prod_zpow, prod_div_distrib]
    _ = ∏ w, u w ^ (2 * e w - k) := prod_congr rfl fun w _ ↦ (zpow_sub₀ (hu_ne w) ..).symm

/-- Let `ν` have weight `e ≠ 0` and some tame part, and let `S` be finite. Then the `L`-function of
`x ↦ ν(x / x̄)` without the factors at `S ∪ S̄` does not vanish at any real `s ≥ 1` (at `s = 1`
its value is the limit from the right, see `New.eulerProd`). -/
lemma L_ne_zero (hS : S.Finite) (he : e ≠ 0) {s : ℝ} (hs : 1 ≤ s) : ν.L S s ≠ 0 := by
  -- The square of the base change has a nonzero type at infinity, so it is not trivial.
  exact h.isHeckeOfType.eulerProd_ne_zero hS.conjClosure
    ((h.isHeckeOfType.pow 2).ne_one (by positivity)) hs

/-- If the tame part `ψ` of `ν` is trivial at `w` and at `w̄`, the base change of `ν` is unramified
at `w`. -/
lemma charUnramifiedAt (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1) :
    CharUnramifiedAt ν.baseChange.finPart w := by
  -- By `exists_baseChange_finPart_locIdele` the value at a local unit `x` is `ψ w` at the reduction
  -- of `x / x̄`, a unit.
  intro x hx
  obtain ⟨h_int, h_eq⟩ := h.exists_baseChange_finPart_locIdele hψ_star x fun _ ↦ hx
  ext
  simp [h_eq, MulChar.one_apply, hψ_w]

/-- Let `ν` have weight `e` and tame part `ψ`, with `ψ w` and `ψ w̄` trivial. Then the Hecke
character `x ↦ ν (x / x̄)` takes mutually inverse values at the chosen uniformisers at `w̄` and at
`w`. -/
lemma atUniformizer_star (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1) :
    ν.baseChange.atUniformizer (star w) = (ν.baseChange.atUniformizer w)⁻¹ := by
  have h_unr : CharUnramifiedAt ν.baseChange.finPart (star w) :=
    h.charUnramifiedAt hψ_star (by rwa [star_star])
  -- Conjugation inverts `x / x̄`, so it inverts the value of the base change.
  have h_div (x : (𝔸f E)ˣ) :
      divStar (.map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)) (star x) : (𝔸 E)ˣ) =
        (divStar (.map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)) x))⁻¹ :=
    Subtype.ext (Prod.ext (star_mul_star _ _) (star_mul' _ _)).symm
  have h_star (x : (𝔸f E)ˣ) : ν.baseChange.finPart (star x) = (ν.baseChange.finPart x)⁻¹ := by
    simp [HeckeChar.finPart, baseChange_apply_coe_toFun, h_div, Units.ext_iff]
  -- The conjugate of the uniformiser at `w` is a uniformiser at `star w`, where `ν.baseChange` is
  -- unramified.
  simpa [star_locIdele, h_unr.apply_locIdele_eq_zpow (.map _ _), HeckeChar.atUniformizer,
    Units.ext_iff]
    using h_star (locIdele w (uniformizer w))

/-- Let ν be a continuous circle-valued character of the norm-one adeles of the CM field E that is
trivial on E. Suppose ν has weight `e` and tame part `ψ`: almost all residue characters ψ_w are
trivial, and ν(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part. If
ψ_v = 1 for all v ∉ S, then `ν⁻¹` and `ν` have the same `L`-function without the factors at
`S ∪ S̄`. -/
theorem L_inv (hS : ∀ v : FinPlace E, v ∉ S → ψ v = 1) : ν⁻¹.L S = ν.L S := by
  -- The Euler factor of `ν⁻¹` at `v` is that of `ν` at `star v`: both coefficients are `0` on
  -- `S ∪ S̄`, and outside it conjugation of the prime inverts the value of the base change.
  let c : FinPlace E → ℂ := heckeCoeff ν.baseChange.finPart S.conjClosure
  have h_coeff (v : FinPlace E) :
      heckeCoeff ν⁻¹.baseChange.finPart S.conjClosure v = c (star v) := by
    have hv_star : star v ∈ S.conjClosure ↔ v ∈ S.conjClosure := by simp [or_comm]
    unfold c heckeCoeff
    by_cases hv : v ∈ S.conjClosure
    · rw [Set.indicator_of_notMem (not_not.mpr hv),
        Set.indicator_of_notMem (not_not.mpr (hv_star.mpr hv))]
    · obtain ⟨hv_out, hv_star_out⟩ : v ∉ S ∧ star v ∉ S := by
        simpa [not_or] using hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem (mt hv_star.mp hv)]
      simpa [HeckeChar.atUniformizer] using
        (h.atUniformizer_star (hS v hv_out) (hS (star v) hv_star_out)).symm
  -- Reindex the sum over the primes by conjugation, which preserves the norm `q`.
  have h_sum (s : ℝ) :
      ∑' v : FinPlace E, Complex.log (1 + -(c (star v) * (v.q : ℂ) ^ (-s : ℂ))) =
        ∑' v : FinPlace E, Complex.log (1 + -(c v * (v.q : ℂ) ^ (-s : ℂ))) := by
    simpa [q_star] using (Function.Involutive.toPerm star star_involutive).tsum_eq
      fun v : FinPlace E ↦ Complex.log (1 + -(c v * (v.q : ℂ) ^ (-s : ℂ)))
  unfold AutChar.L eulerProd
  simp only [h_coeff, h_sum]
  rfl

include hψ_w hψ_star

variable [WeilData E] (k j : ℤ)

open scoped Classical in
/-- For a character ν of U(1)(𝔸) of weight e, the algebraic Hecke character ν(x/x̄) υ(x)^{−k}
|x|^{j−k/2}, of infinity type j + e − k on the CM type, j − e on its conjugate. -/
def toAlgebraic : AlgHeckeChar E :=
  IsHeckeOfType.toAlgebraic (k := 2 * j - k)
    (m :=
      fun σ ↦
        j +
          if σ = Φ (NumberField.InfinitePlace.mk σ) then
            e (NumberField.InfinitePlace.mk σ) - k
          else
            -e (NumberField.InfinitePlace.mk σ))
    (by simp +arith)
    ((ν.baseChange * (υ ^ k)⁻¹).isHeckeOfType_finPart fun z ↦ by
      -- The type at infinity is `2 * e w - k = (j + (e w - k)) - (j - e w)`.
      rw [h.baseChange_mul_upsilon_zpow_inv_apply k _ rfl]
      refine prod_congr rfl fun w _ ↦ ?_
      congr 1
      simp +arith)

/-- The algebraic character made from `ν` is unramified at `w` if the tame part of `ν` is trivial at
`w` and at `w̄` (the section hypotheses `hψ_w`, `hψ_star`). -/
lemma charUnramifiedAt_toAlgebraic : CharUnramifiedAt (h.toAlgebraic k j).val.fst w := by
  -- The three factors `baseChange ν`, `υ` and the absolute value are each trivial on a local unit
  -- `u`.
  intro u hu
  ext
  simp [toAlgebraic, h.charUnramifiedAt hψ_w hψ_star u hu, charUnramifiedAt_upsilon w u hu, hu]

end AutChar.HasWeight

end AutCharLFunction

/-!
## Base change of algebraic Hecke characters

An element `ω` of `New.AlgHeckeChar E` is a pair `(θ, n)`, where `θ = ω.1.1` is a character of the
finite ideles with open kernel, `n = ω.1.2.toAdd` is its type, and `θ(x) = ∏_σ σ(x) ^ (-n_σ)` on
`Eˣ`.
-/

section AlgHeckeBaseChange

variable {E K₀ : Type _} [Field E] [EmbeddedNumberField E] [Field K₀] [NumberField K₀]

open Units Fintype

/-- For the norm from `E` to `K₀`: `∏ s, s (N x) ^ n s = ∏ σ, σ x ^ n (σ|K₀)`, the products running
over the complex embeddings of `K₀` and of `E`. -/
lemma prod_norm_zpow [Algebra K₀ E] (x : E) (n : (K₀ →+* ℂ) → ℤ) :
    ∏ s : K₀ →+* ℂ, s (Algebra.norm K₀ x) ^ n s =
      ∏ σ : E →+* ℂ, σ x ^ n (σ.comp (algebraMap K₀ E)) := by
  classical
  -- Group the `σ` by their restriction `s`; the norm is the product over the `σ` that extend `s`.
  rw [← prod_fiberwise fun σ : E →+* ℂ ↦ σ.comp (algebraMap K₀ E)]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  let s_algebra : Algebra K₀ ℂ := s.toAlgebra
  let extensions : {σ : E →+* ℂ // σ.comp (algebraMap K₀ E) = s} ≃ (E →ₐ[K₀] ℂ) :=
    { toFun σ := ⟨σ.val, RingHom.congr_fun σ.prop⟩
      invFun τ := ⟨τ, τ.comp_algebraMap⟩ }
  rw [show s (Algebra.norm K₀ x) = ∏ τ : E →ₐ[K₀] ℂ, τ x from Algebra.norm_eq_prod_embeddings ..,
    ← Finset.prod_zpow]
  exact (prod_equiv extensions _ (fun τ ↦ τ x ^ n s)
    fun σ ↦ congrArg (fun t ↦ σ.val x ^ n t) σ.prop).symm

/-- Base change `ω ∘ N` to `E` of an algebraic Hecke character `ω` of `K₀`; its exponent at an
embedding `σ` of `E` is that of `ω` at `σ|K₀`. -/
noncomputable def AlgHeckeChar.baseChange [Algebra K₀ E] (ω : AlgHeckeChar K₀) :
    AlgHeckeChar E where
  val :=
    (ω.val.1.comp (Units.map (adeleNorm K₀ E)),
      Multiplicative.ofAdd fun σ ↦ ω.val.2.toAdd (σ.comp (algebraMap K₀ E)))
  property := by
    refine ⟨ω.property.1.preimage (by fun_prop), fun x ↦ ?_⟩
    -- On a principal idele the norm of ideles is the norm of the fields.
    calc
      (ω.val.1 (map (adeleNorm K₀ E) (principalIdele x)) : ℂ)
      _ = ω.val.1 (principalIdele (x.map (Algebra.norm K₀))) :=
        congrArg (fun y ↦ (ω.val.1 y : ℂ)) (map_adeleNorm_principalIdele x)
      _ = ∏ s : K₀ →+* ℂ, s (Algebra.norm K₀ x.val) ^ (-ω.val.2.toAdd s) := ω.property.2 _
      _ = _ := prod_norm_zpow x.val _

end AlgHeckeBaseChange

end New

end
