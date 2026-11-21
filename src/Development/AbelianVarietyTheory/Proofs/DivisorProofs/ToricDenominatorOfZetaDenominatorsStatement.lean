import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf

section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_iff_placewise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E, z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), Valued.v (z w - a w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  first | exact @GlobalTheory.CMVal.HatPlace.mem_hatO_iff | exact GlobalTheory.CMVal.HatPlace.mem_hatO_iff | (intros; apply GlobalTheory.CMVal.HatPlace.mem_hatO_iff <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]

open Classical in

theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove
end
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

noncomputable section

namespace GlobalTheory.LatValSum

theorem norm_le_one_of_isIntegral_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one {q : ℕ} [Fact q.Prime] {n : ℕ} (hn : n.Coprime q) : ‖(n : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q]) := (map_natCast _ n).symm
  rw [e]
  have h : ‖algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q])‖ = ‖((n : ℕ) : ℚ_[q])‖ := PadicComplex.norm_extends' (p := q) _
  rw [h]
  exact Padic.norm_natCast_eq_one_iff.mpr hn.symm

local notation "K" => algebraicClosure ℚ ℂ

theorem valGe_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) →
    (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  intro l hl r J _ u x hu hx
  haveI : Fact l.Prime := ⟨hl⟩
  have hx' := fun j => (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r (x j ^ 12)).1 (hx j)
  refine (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r _).2 ?_
  intro lam

  have huK : ∀ j, ∃ h : u j ∈ K, ‖lam ⟨u j, h⟩‖ ≤ 1 := by
    intro j
    obtain ⟨n, hn, hint⟩ := hu j
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by
        rintro rfl
        exact hl.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)
      exact_mod_cast this
    have hmK : (n : ℂ) * u j ∈ K :=
      mem_algebraicClosure_iff.mpr (hint.tower_top (A := ℚ)).isAlgebraic
    have hnK : (n : ℂ) ∈ K := IntermediateField.natCast_mem (algebraicClosure ℚ ℂ) n
    have huj : u j = ((n : ℂ) * u j) * (n : ℂ)⁻¹ := by field_simp
    have hK : u j ∈ K := by rw [huj]; exact (algebraicClosure ℚ ℂ).mul_mem hmK ((algebraicClosure ℚ ℂ).inv_mem hnK)
    refine ⟨hK, ?_⟩
    have he : (⟨(n : ℂ) * u j, hmK⟩ : K) = (n : K) * ⟨u j, hK⟩ := Subtype.ext (by simp)
    have hI : IsIntegral ℤ (lam ⟨(n : ℂ) * u j, hmK⟩) := by
      have h2 : IsIntegral ℤ (⟨(n : ℂ) * u j, hmK⟩ : K) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K ℂ) Subtype.val_injective).mp hint
      convert map_isIntegral_int lam h2
      exact Subsingleton.elim _ _
    have h1 := norm_le_one_of_isIntegral_int hI
    rw [he, map_mul, map_natCast, norm_mul, norm_natCast_eq_one hn, one_mul] at h1
    exact h1

  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hpow : ((l : ℝ) ^ (r / 12)) ^ (12 : ℕ) = (l : ℝ) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hxK : ∀ j, ∃ h : x j ∈ K, ‖lam ⟨x j, h⟩‖ ≤ (l : ℝ) ^ (r / 12) := by
    intro j
    obtain ⟨h12, hb⟩ := hx' j lam
    have hK : x j ∈ K := mem_algebraicClosure_iff.mpr
      ((mem_algebraicClosure_iff.mp h12).of_pow (by norm_num))
    refine ⟨hK, ?_⟩
    have he : (⟨x j ^ 12, h12⟩ : K) = (⟨x j, hK⟩ : K) ^ 12 := Subtype.ext (by simp)
    rw [he, map_pow, norm_pow, ← hpow] at hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hb
  choose hu1 hu2 using huK
  choose hx1 hx2 using hxK
  have hSK : (∑ j, u j * x j) ∈ K := (algebraicClosure ℚ ℂ).sum_mem fun j _ => (algebraicClosure ℚ ℂ).mul_mem (hu1 j) (hx1 j)
  have hS12 : (∑ j, u j * x j) ^ 12 ∈ K := (algebraicClosure ℚ ℂ).pow_mem hSK 12
  refine ⟨hS12, ?_⟩
  have he : (⟨(∑ j, u j * x j) ^ 12, hS12⟩ : K) = (∑ j, (⟨u j, hu1 j⟩ : K) * ⟨x j, hx1 j⟩) ^ 12 :=
    Subtype.ext (by simp)
  rw [he, map_pow, norm_pow, ← hpow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 12
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [map_mul, norm_mul]
  calc ‖lam ⟨u j, hu1 j⟩‖ * ‖lam ⟨x j, hx1 j⟩‖ ≤ 1 * (l : ℝ) ^ (r / 12) :=
        mul_le_mul (hu2 j) (hx2 j) (norm_nonneg _) zero_le_one
    _ = (l : ℝ) ^ (r / 12) := one_mul _

end GlobalTheory.LatValSum
end
end

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  atlas_forward_decl GlobalTheory.LatValSum.valGe_sum_pow_twelve
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomRow

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem beta_eq_pow (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ^ 12 = latDisc Λ) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
  rw [beta, div_pow, ← pow_mul, mul_comm _ 12, pow_mul, hΩ]

theorem classTerm_rep [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    (hc : c ≠ ⊥) {χ : HChar E} (hinf : HasInf χ φ (fun i => (κ i : ℤ) + s)) (htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1)
    {l : ℕ} (hl : l.Prime) (hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S)
    (y : (Af E)ˣ) (S : ℂ → ℂ) (hS : IsLatSum φ (2 * s) κ (lattice c y) S) :
    ∃ y' : (Af E)ˣ, OneOver l y' ∧ ∃ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' ∧ ∃ u : ℂ, IntAt l u ∧
      ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = u * S' 0 := by
  obtain ⟨y', hy', hone⟩ := GlobalTheory.CMVal.TrivAbove.exists_rep_trivial_above E c l hc hl (QuotientGroup.mk y)
  obtain ⟨S', hS'⟩ := hex y'
  refine ⟨y', hone, S', hS', ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹, ?_, ?_⟩
  · have hu := GlobalTheory.CMVal.value_unitAt E I φ hφ s κ c χ l hc hl hinf htriv y' fun w hw => by
      rw [hone w hw, map_one]
    exact (GlobalTheory.CMVal.LUnit.unitAt_inv hu).2.1
  · exact GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ c χ hinf htriv y y' S S' hy'.symm hS hS'

theorem toricDenominator (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hR : LatIntRam) (hU : LatIntUnr) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  have hzc : IsClassZetaVals (2 * s) z := hz
  refine ⟨z, hzc, fun κ 𝔣 Λ χ hb hΛ hχ => ?_⟩
  have hUr : UnramFin E := hd.2.2.1
  have hφ : IsCMType φ := hd.2.2.2.2.2.2.1
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  intro l hl Q hQ hQl
  set c := condQ 𝔣 Q with hcdef
  have hc : c ≠ ⊥ := mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  have h0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hUr hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1 := fun u hu => h0 u (hatOUnits_mono hle hu)
  have hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := fun y =>
    GlobalTheory.CMVal.LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 c χ hUr hs hb
      (dvd_mul_right _ _) hc hχ.1 hχ.2.2.1 htriv y
  set x : ℂ → ℂ := fun T => (C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ with hxdef
  have hx : ∀ T, beta E d s κ Λ T = x T ^ 12 := fun T => beta_eq_pow d s κ Λ hΩ T
  have hxmul : ∀ u T, x (u * T) = u * x T := fun u T => by simp only [hxdef]; ring

  have hlat : ∀ y' : (Af E)ˣ, OneOver l y' → ∀ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (x (S' 0) ^ 12) := fun y' hy' S' hS' => by
    rw [← hx]
    by_cases h : c_vp 𝔣 l = 0
    · exact hU E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'
    · exact hR E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'

  have hterm : ∀ χ' : HChar E, HasInf χ' φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ' u = 1) →
      ∀ (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice c y) S →
      ∃ u w : ℂ, IntAt l u ∧ ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (w ^ 12) ∧
        x (((finPart χ' y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0) = u * w := by
    intro χ' hinf' htriv' y S hS
    obtain ⟨y', hy', S', hS', u, hu, e⟩ := classTerm_rep hφ hc hinf' htriv' hl hex y S hS
    exact ⟨u, x (S' 0), hu, hlat y' hy' S' hS', by rw [e, hxmul]⟩
  refine ⟨fun y T ⟨S, hS, hT⟩ => ?_, fun ψ T hψ ⟨hfin, S, hS, hT⟩ => ?_⟩
  · obtain ⟨u, w, hu, hw, e⟩ := hterm χ hχ.2.2.1 htriv y S hS
    have := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) Unit (fun _ => u) (fun _ => w) (fun _ => hu) (fun _ => hw)
    rw [hx, hT, e]
    simpa using this
  · have hinf' : HasInf (χ * ψ) φ (fun i => (κ i : ℤ) + s) := hχ.2.2.1.mul_triv hψ.1
    have htriv' : ∀ u ∈ hatOUnits c, finPart (χ * ψ) u = 1 := fun u hu => by
      show finPart χ u * finPart ψ u = 1
      rw [htriv u hu, hψ.2 u hu, one_mul]
    have := Fintype.ofFinite (PicO c)
    choose u w hu hw e using fun q : PicO c => hterm (χ * ψ) hinf' htriv' q.out (S q) (hS q)
    have key := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) (PicO c) u w hu hw
    rw [hx, hT, finsum_eq_sum_of_fintype]
    have : x (∑ q, ((finPart (χ * ψ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) = ∑ q, u q * w q := by
      rw [← Finset.sum_congr rfl fun q _ => e q]
      simp only [hxdef, Finset.mul_sum, Finset.sum_div]
    rw [this]
    exact key

end GlobalTheory.ToricDenomRow
end
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_denominator_of_zeta_denominators : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → LatIntRam → LatIntUnr → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  first | exact @GlobalTheory.ToricDenomRow.toricDenominator | exact GlobalTheory.ToricDenomRow.toricDenominator | (intros; apply GlobalTheory.ToricDenomRow.toricDenominator <;> assumption)
end
