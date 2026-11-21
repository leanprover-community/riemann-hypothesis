import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.ImportsAlt
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import ReciprocityTheory.DualLattices.SumInvMulTrace
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardLe
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraFurther

section
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_character_order_generates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | exact GlobalTheory.CompanionTheory.Ar.GR.FundGen.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.FundGen.main <;> assumption)
end

section
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem val_one_sub_pow_le {K : Type} [Field K] (v : Valuation K NNReal) {x : K} (hx : v x = 1)
    (i : ℕ) : v (1 - x ^ i) ≤ v (1 - x) := by
  have h : 1 - x ^ i = (1 - x) * ∑ j ∈ Finset.range i, x ^ j := (mul_neg_geom_sum x i).symm
  rw [h, map_mul]
  refine mul_le_of_le_one_right' ?_
  exact v.map_sum_le (fun j _ => by rw [map_pow, hx, one_pow])

theorem val_eq_one_of_pow_eq_one {K : Type} [Field K] (v : Valuation K NNReal) {x : K} {n : ℕ}
    (hn : n ≠ 0) (hx : x ^ n = 1) : v x = 1 := by
  have h : v x ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_left_inj₀ zero_le zero_le_one hn).mp (by simpa using h)

theorem val_sub_one_pow {K : Type} [Field K] (v : Valuation K NNReal) (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  have hprod : (p : K) = ∏ μ ∈ primitiveRoots p K, (1 - μ) := by
    rw [← Polynomial.eval_one_cyclotomic_prime (R := K) (p := p),
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
    simp
  have hval : ∀ μ ∈ primitiveRoots p K, v (1 - μ) = v (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    refine le_antisymm (val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero
      hζ.pow_eq_one) i) ?_
    conv_lhs => rw [← hj]
    exact val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero hμ'.pow_eq_one) j
  rw [hprod, map_prod, Finset.prod_congr rfl hval, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp, Valuation.map_sub_swap]

theorem exists_mulShift_eq {F K : Type} [Field F] [Fintype F] [Field K] (ψ₀ ψ : AddChar F K)
    (h₀ : ψ₀ ≠ 1) : ∃ c, ψ = AddChar.mulShift ψ₀ c :=
  _root_.UpperTheory.Reformulated.B.Yde4.main ψ₀ ψ h₀

def ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

theorem mem_ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ ltOneIdeal v R hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem ltOneIdeal_isPrime {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : (ltOneIdeal v R hv).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : R) ∈ ltOneIdeal v R hv := h ▸ Submodule.mem_top
    rw [mem_ltOneIdeal] at h1
    simp at h1
  · rw [mem_ltOneIdeal, map_mul, map_mul] at hab
    by_contra hcon
    push Not at hcon
    simp only [mem_ltOneIdeal, not_lt] at hcon
    have ha : v (algebraMap R C a) = 1 := le_antisymm (hv.map_le_one a) hcon.1
    have hb : v (algebraMap R C b) = 1 := le_antisymm (hv.map_le_one b) hcon.2
    simp [ha, hb] at hab

theorem gauss_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard hF σ hσ ψ hψ
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI hprime : (ltOneIdeal v R hv).IsPrime := ltOneIdeal_isPrime v R hv

  have hpm : (p : R) ∈ ltOneIdeal v R hv := by
    rw [mem_ltOneIdeal, map_natCast]; exact hp
  have hspan : Ideal.span {(p : R)} ≤ ltOneIdeal v R hv :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpm
  let ι : F →+* R ⧸ ltOneIdeal v R hv :=
    { toFun := fun a => Ideal.Quotient.mk _ (σ a)
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp [MulChar.map_zero]
      map_add' := fun a b => by
        rw [← map_add, Ideal.Quotient.eq]
        have := hspan (hσ a b)
        rwa [sub_sub] at this }

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hvζ : v ζ = 1 := val_eq_one_of_pow_eq_one v hpp.ne_zero hζ.pow_eq_one
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvζ.le
  have hzp : z ^ p = 1 := hv.hom_inj (by rw [map_pow, hζ.pow_eq_one, map_one])
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨y, hym, hy⟩ := ReciprocityTheory.PGsh.gaussCongruence p F R (ltOneIdeal v R hv) ι σ z hF hzp
    (fun a => rfl)

  let ψ₀ : AddChar F C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ₀ : ∀ a, ψ₀ a = algebraMap R C z ^ (Algebra.trace (ZMod p) F a).val := fun a => rfl
  have hψ₀1 : ψ₀ ≠ 1 := by
    haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
    obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod p) F 1
    intro h
    have h1 : ψ₀ b = 1 := by rw [h]; simp
    rw [hψ₀] at h1
    have hb0 : (Algebra.trace (ZMod p) F b).val ≠ 0 := by
      rw [hb, Ne, ZMod.val_eq_zero]
      exact one_ne_zero
    exact hζ.pow_ne_one_of_pos_of_lt hb0 (ZMod.val_lt _) h1
  obtain ⟨c, rfl⟩ := exists_mulShift_eq ψ₀ ψ hψ₀1
  have hc : c ≠ 0 := by
    rintro rfl
    exact hψ (AddChar.mulShift_zero _)
  have hσc : σ c * σ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  have hsum : ∑ a, algebraMap R C (σ⁻¹ a) * AddChar.mulShift ψ₀ c a =
      algebraMap R C (σ c) * ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ (fun a => ?_)
    simp only [Equiv.mulLeft₀_apply, AddChar.mulShift_apply, map_mul, ← mul_assoc]
    rw [← map_mul, hσc, map_one, one_mul]
  have hvσ : v (algebraMap R C (σ c)) = 1 := by
    have h1 : v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) = 1 := by
      rw [← map_mul, ← map_mul, hσc, map_one, map_one]
    refine le_antisymm (hv.map_le_one _) ?_
    calc (1 : NNReal) = v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) := h1.symm
      _ ≤ v (algebraMap R C (σ c)) := mul_le_of_le_one_right' (hv.map_le_one _)
  have hG : ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b =
      (algebraMap R C z - 1) * (algebraMap R C y - 1) := by
    have := congrArg (algebraMap R C) hy
    simp only [map_sum, map_mul, map_pow, map_sub, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by rw [hψ₀]
  have hvy : v (algebraMap R C y - 1) = 1 := by
    have h : v (algebraMap R C y) < v (1 : C) := by
      rw [map_one]; exact hym
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left v h, map_one]
  rw [hsum, hG, map_mul, map_mul, hvσ, hvy, one_mul, mul_one]
  exact val_sub_one_pow v p hζ

end GlobalTheory.CompanionTheory.Ar.GR
end

open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_valuation_teichmuller : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.gauss_value
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_character_ideal_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.r_decomp_relay | exact GlobalTheory.CompanionTheory.Ar.GR.r_decomp_relay | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.r_decomp_relay <;> assumption)
end

section
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem rank_one_dual_gauss : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable F AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) :=
  @PositivityTheory.HtPt.Ri.r_dual

end GlobalTheory.CompanionTheory.Ar.GR
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_hopf_order_gauss_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable F AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GR.rank_one_dual_gauss
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem exists_addChar_ne_one (C F : Type) [Field C] [IsAlgClosed C] [CharZero C] [Field F]
    [Finite F] : ∃ ψ : AddChar F C, ψ ≠ 1 := by
  have hch : ringChar C ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  let P := AddChar.FiniteField.primitiveChar F C hch
  haveI : NeZero (P.n : ℕ) := ⟨P.n.ne_zero⟩
  haveI : Algebra.IsIntegral C (CyclotomicField P.n C) :=
    IsCyclotomicExtension.integral {(P.n : ℕ)} C _
  let j : CyclotomicField P.n C →ₐ[C] C := IsAlgClosed.lift
  let ψ : AddChar F C :=
    { toFun := fun a => j (P.char a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp [AddChar.map_add_eq_mul] }
  refine ⟨ψ, fun h => ?_⟩
  refine P.prim one_ne_zero ?_
  ext a
  have h1 : j (P.char a) = 1 := by
    have := congrArg (fun χ : AddChar F C => χ a) h
    simpa [ψ] using this
  have h2 : P.char a = 1 := j.toRingHom.injective (by simpa using h1)
  simpa [AddChar.mulShift_apply] using h2

theorem exists_shift_equiv {C F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    ∃ e : F ≃ AddChar F C, (∀ h h', e (h + h') = e h * e h') ∧ ∀ h a, e h a = ψ (h * a) :=
  _root_.UpperTheory.Reformulated.B.AddCharacterCount.main ψ hψ

theorem rank_one_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∃ AD : HopfOrder (C := C) R F, FStable F AD.carrier ∧ (∀ cN cD, HasColen R v AA.carrier cN → HasColen R v AD.carrier cD → (cN * cD) ^ 2 = v (p : C) ^ (f * p ^ f)) ∧ ∀ τ : MulChar F R, IsFund p τ → ∀ c cD : R, xIdeal AA.carrier τ = Ideal.span {c} → xIdeal AD.carrier τ = Ideal.span {cD} → (v (algebraMap R C c) * v (algebraMap R C cD)) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hcard AA hFS
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one C F
  obtain ⟨e, he, heψ⟩ := exists_shift_equiv ψ hψ
  obtain ⟨AD, hAD, -, hcol⟩ := h1 C R v hv F F e he rfl AA
  have hfun : (fun (h a : F) => e h a) = fun (h a : F) => ψ (h * a) := by
    funext h a; exact heψ h a
  rw [hfun] at hAD
  obtain ⟨hFD, hdual⟩ := GlobalTheory.T.dual_hopf_order_gauss_sum p C v R hv hvp F f hcard AA hFS ψ hψ AD hAD
  refine ⟨AD, hFD, ?_, ?_⟩
  · intro cN cD hN hD
    rw [hcol cN cD hN hD, hcard, Nat.cast_pow, map_pow, ← pow_mul]
  · intro τ hτ c cD hc hcD
    have hord := (GlobalTheory.T.teichmuller_character_order_generates p C v R hv hvp F f hcard τ hτ).1
    by_cases h2 : Fintype.card F = 2
    · have hpf : p ^ f = 2 := hcard.symm.trans h2
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hpf
      have ht : τ = 1 := orderOf_eq_one_iff.1 (by rw [hord]; norm_num)
      have hN := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AA hFS τ hτ (fun _ => c)
        (fun m => by rw [ht, one_pow, ← ht]; exact hc)).2.2
      have hD := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AD hFD τ hτ (fun _ => cD)
        (fun m => by rw [ht, one_pow, ← ht]; exact hcD)).2.2
      have hI : Finset.Icc 1 (2 ^ 1 - 1) = ({1} : Finset ℕ) := by decide
      rw [hI, Finset.prod_singleton] at hN hD
      have key := hcol _ _ hN hD
      rw [h2] at key
      have := (pow_left_inj₀ zero_le zero_le two_ne_zero).1 key
      simpa using this
    · have hne : τ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        apply h2
        rw [hcard]
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        omega
      rw [hdual τ hne c cD hc hcD]
      exact GlobalTheory.T.gauss_sum_valuation_teichmuller p C v R hv hvp F f hcard h2 τ hτ ψ hψ

end GlobalTheory.CompanionTheory.Ar.GR
end
