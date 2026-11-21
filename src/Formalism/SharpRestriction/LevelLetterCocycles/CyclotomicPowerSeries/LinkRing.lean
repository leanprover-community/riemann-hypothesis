import Mathlib
import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EmultiplicityEqValuation
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval

section
noncomputable section

namespace LevelStatements.Link

open PowerSeries

theorem pow_val_mem_primitiveRoots {LL : Type} [Field LL] (N : ℕ) (hN : 0 < N) (w : ZMod N)
    (hw : IsUnit w) {ξ : LL} (hξ : ξ ∈ primitiveRoots N LL) : ξ ^ w.val ∈ primitiveRoots N LL := by
  obtain ⟨u, rfl⟩ := hw
  rw [mem_primitiveRoots hN] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)

theorem eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] (s : ℕ) (a b : ZMod (l ^ (s + 1)))
    (ha : a ^ (l - 1) = 1) (hb : b ^ (l - 1) = 1) (hab : (l : ZMod (l ^ (s + 1))) ∣ b - a) :
    b = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  set x := b - a with hx
  have hba : b = a + x := by rw [hx]; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion
    (Polynomial.X ^ (l - 1) : Polynomial (ZMod (l ^ (s + 1)))) a x
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  rw [← hba, ha, hb] at hk
  have hlpow : (l : ZMod (l ^ (s + 1))) ^ (s + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hxpow : x ^ (s + 1) = 0 := by
    obtain ⟨t, ht⟩ := hab
    rw [ht, mul_pow, hlpow, zero_mul]
  have hkx : IsNilpotent (k * x) := ⟨s + 1, by rw [mul_pow, hxpow, mul_zero]⟩
  have hl1 : IsUnit ((l - 1 : ℕ) : ZMod (l ^ (s + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hinv : a * a ^ (l - 1 - 1) = 1 := by
    rw [← pow_succ', show l - 1 - 1 + 1 = l - 1 by omega, ha]
  have ha' : IsUnit a := ⟨⟨a, a ^ (l - 1 - 1), hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩
  have hU : IsUnit (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) :=
    hkx.isUnit_add_left_of_commute (hl1.mul (ha'.pow _)) (Commute.all _ _)
  have hx0 : x * (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) = 0 := by
    linear_combination (-1 : ZMod (l ^ (s + 1))) * hk
  have hx' : x = 0 := hU.mul_left_eq_zero.mp hx0
  exact sub_eq_zero.mp hx'

theorem exists_toZModPow_eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] {Δ : Type*} (om : Δ → ℤ_[l])
    (hom : ∀ j, om j ^ (l - 1) = 1)
    (hom' : ∀ a : ZMod l, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a) (s : ℕ)
    (a : ZMod (l ^ (s + 1))) (ha : a ^ (l - 1) = 1) :
    ∃ j, PadicInt.toZModPow (s + 1) (om j) = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : l ∣ l ^ (s + 1) := dvd_pow_self l (Nat.succ_ne_zero s)
  set π := ZMod.castHom hdvd (ZMod l) with hπ
  have hψ : π.comp (PadicInt.toZModPow (s + 1)) = (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    apply ZMod.ringHom_eq_of_ker_eq
    have m1 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (π.comp (PadicInt.toZModPow (s + 1))))
    have m2 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l))
    rw [IsLocalRing.eq_maximalIdeal m1, IsLocalRing.eq_maximalIdeal m2]
  have key : ∀ y : ZMod (l ^ (s + 1)), π y = 0 → (l : ZMod (l ^ (s + 1))) ∣ y := by
    intro y hy
    rw [← ZMod.natCast_zmod_val y, map_natCast] at hy
    obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod l) l y.val).mp hy
    refine ⟨(t : ZMod (l ^ (s + 1))), ?_⟩
    rw [← ZMod.natCast_zmod_val y, ht, Nat.cast_mul]
  have ha0 : π a ≠ 0 := by
    intro h0
    have hpa : π a ^ (l - 1) = 1 := by rw [← map_pow, ha, map_one]
    rw [h0, zero_pow (by omega)] at hpa
    exact zero_ne_one hpa
  obtain ⟨j, hj⟩ := hom' (π a) ha0
  refine ⟨j, eq_of_pow_pred_eq_one s a _ ha ?_ ?_⟩
  · rw [← map_pow, hom j, map_one]
  · have hc : π (PadicInt.toZModPow (s + 1) (om j)) = PadicInt.toZMod (om j) :=
      RingHom.congr_fun hψ (om j)
    have hk : π (PadicInt.toZModPow (s + 1) (om j) - a) = 0 := by
      rw [map_sub, hc, hj, sub_self]
    exact key _ hk

theorem map_cyclotomic_comp {O LL : Type} [CommRing O] [Field LL] [CharZero LL] [Algebra O LL]
    (ρ : PowerSeries O →ₐ[O] PowerSeries LL) (ζ : LL) (hρ : 1 + ρ X = C ζ * exp LL) (m : ℕ) :
    ρ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      Polynomial.aeval (C ζ * exp LL) (Polynomial.cyclotomic m LL) := by
  have key : ∀ p : Polynomial O, ρ (p : PowerSeries O) = Polynomial.aeval (ρ X) p := by
    intro p
    have h := Polynomial.algHom_ext (f := ρ.comp (Polynomial.coeToPowerSeries.algHom O))
      (g := Polynomial.aeval (ρ X)) (by simp)
    have hp := AlgHom.congr_fun h p
    simpa using hp
  rw [key, Polynomial.aeval_comp]
  have h1 : Polynomial.aeval (ρ X) (Polynomial.X + 1 : Polynomial O) = C ζ * exp LL := by
    rw [map_add, Polynomial.aeval_X, map_one, add_comm, hρ]
  rw [h1, ← Polynomial.map_cyclotomic m (algebraMap O LL), Polynomial.aeval_map_algebraMap]

end LevelStatements.Link
end
end

section
noncomputable section

namespace LevelStatements.Link

open PowerSeries IsLocalRing Formalism.ExponentWindows

abbrev Ks (LL : Type) [Field LL] (l s : ℕ) : Type :=
  ↥(primitiveRoots (l ^ (s + 1)) LL) → LL

theorem linkRing

    (hUnique : LevelStatements.Lv.RhoUniqueStatement) (hCompl : LevelStatements.Lv.SplitComplStatement)
    (hSimple : LevelStatements.Lv.CycloSimpleStatement) (hCop : LevelStatements.Lv.PsCoprimeStatement)
    (hUnit : LevelStatements.Lv.RhoUnitStatement) (hDesc : LevelStatements.Lv.DescendDvdStatement)
    (hPi : LevelStatements.Lv.PiSeriesStatement)

    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    {LL : Type} [Field LL] [CharZero LL] [Algebra O LL] [IsFractionRing O LL]
    (ϖ : O) (hϖ : Irreducible ϖ)

    {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]
    {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
    (S : E.LevelData L c ell Λ r) {Δ D : Type} [AddCommGroup D] [Module LL D]
    [hℓ : Fact B.ℓ.Prime] (hℓ2 : B.ℓ ≠ 2) (hℓm : (B.ℓ : O) ∈ maximalIdeal O)
    (n0 : ℕ) (hn0 : ell ≤ n0) (hroot : ∃ ζ : LL, IsPrimitiveRoot ζ (B.ℓ ^ n0))

    (ι : PowerSeries O →ₐ[O] PowerSeries O) (w : (PowerSeries O)ˣ)
    (G1 : ι X = (w : PowerSeries O) * X ^ (B.ℓ - 1))

    (φπ : PowerSeries O →ₐ[O] PowerSeries O) (hφπ : φπ X = (1 + X) ^ B.ℓ - 1)
    (G3 : ∀ a, ι (B.φ a) = φπ (ι a))

    (hPs : LevelStatements.Lv.PsCycloStatement)
    (G2 : ∃ v : (PowerSeries O)ˣ, ι B.q = (v : PowerSeries O) *
      (((Polynomial.cyclotomic B.ℓ O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O))

    (ρζ : LL → (PowerSeries O →ₐ[O] PowerSeries LL))
    (hρζ : ∀ s < ell, ∀ ζ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, 1 + ρζ ζ X = C ζ * exp LL)

    (R : G.LevelModel S LL (fun s => Ks LL B.ℓ s) Δ D)
    (hρ : ∀ s < ell, ∀ (a : PowerSeries O) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s a) = ρζ ζ (ι a))
    (u : Oˣ) (uZ : ℤ_[B.ℓ]) (huZ : (uZ - 1).valuation = 1)
    (ιZ : ℤ_[B.ℓ] →+* O) (hutie : ιZ uZ = (u : O))
    (hu : ∀ s < ell, ((R.lev s).u : LL) = algebraMap O LL (u : O))
    (hσ : ∀ s < ell, ∀ (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) uZ).val → (R.lev s).σ f ζ = f ζ')
    (om : Δ → ℤ_[B.ℓ]) (hom : ∀ j, om j ^ (B.ℓ - 1) = 1)
    (hom' : ∀ a : ZMod B.ℓ, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a)
    (hτ : ∀ s < ell, ∀ j (f : Ks LL B.ℓ s) (ζ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      (ζ' : LL) = (ζ : LL) ^ (PadicInt.toZModPow (s + 1) (om j)).val → (R.lev s).τ j f ζ = f ζ') :
    R.K1b ∧ R.HasU u ∧ (∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s ∧ (R.lev s).PhiGammaCommute) ∧ R.UnitsAt ∧ R.Compl ϖ := by
  have hp : B.ℓ.Prime := hℓ.out
  have hl1 : 0 < B.ℓ - 1 := by have := hp.two_le; omega
  have hpos : ∀ s, 0 < B.ℓ ^ (s + 1) := fun s => pow_pos hp.pos _
  have hprim : ∀ s (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      IsPrimitiveRoot (ζ : LL) (B.ℓ ^ (s + 1)) :=
    fun s ζ => (mem_primitiveRoots (hpos s)).1 ζ.2

  have hit : ∀ s a, ι ((⇑B.φ)^[s] a) = (⇑φπ)^[s] (ι a) := by
    intro s
    induction s with
    | zero => intro a; rfl
    | succ s ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', G3, ih]

  have hG : ∀ s, ∃ w' : (PowerSeries O)ˣ, ι (B.p s) = (w' : PowerSeries O) *
      (((Polynomial.cyclotomic (B.ℓ ^ (s + 1)) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
    intro s
    obtain ⟨v, hv⟩ := G2
    unfold Formalism.ExponentWindows.E.Base.p
    rw [hit]
    exact hPs O B.ℓ hp φπ hφπ (ι B.q) v hv s

  have hcyc : ∀ s < ell, ∀ (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)) (m : ℕ),
      ρζ ζ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
        Polynomial.aeval (C (ζ : LL) * exp LL) (Polynomial.cyclotomic m LL) :=
    fun s hs ζ m => map_cyclotomic_comp (ρζ ζ) ζ (hρζ s hs (ζ : LL) ζ.2) m

  have hK1b : R.K1b := by
    intro s hs
    obtain ⟨w', hw'⟩ := hG s
    have hcomp : ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL), ∃ U : (PowerSeries LL)ˣ,
        PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (R.ρ s (B.p s)) =
          (U : PowerSeries LL) * X := by
      intro ζ
      obtain ⟨U, hU⟩ := hSimple LL LL (B.ℓ ^ (s + 1)) (hpos s) (ζ : LL) (exp LL)
        ((hprim s ζ).isRoot_cyclotomic (hpos s)) (constantCoeff_exp (A := LL)) (derivative_exp LL)
      refine ⟨Units.map (ρζ ζ).toMonoidHom w' * U, ?_⟩
      rw [hρ s hs, hw', map_mul, hcyc s hs, hU, Units.val_mul, Units.coe_map, mul_assoc]
      rfl
    choose U hU using hcomp
    have hdvd : (X : PowerSeries (Ks LL B.ℓ s)) ^ 1 ∣ R.ρ s (B.p s) :=
      (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s (B.p s))).1 1).2 fun ζ => by
        rw [hU ζ, pow_one]
        exact dvd_mul_left _ _
    obtain ⟨G, hG'⟩ := hdvd
    have hGu : IsUnit G := by
      refine (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 G).2).2 fun ζ => ?_
      have h := hU ζ
      rw [hG', map_mul, map_pow, map_X, pow_one, mul_comm] at h
      rw [mul_right_cancel₀ X_ne_zero h]
      exact (U ζ).isUnit
    refine ⟨hGu.unit, ?_⟩
    rw [IsUnit.unit_spec, hG', pow_one, mul_comm]

  have hUnits : R.UnitsAt := by
    intro s hs
    have hcomp : ∀ F : PowerSeries O, (∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        IsUnit (ρζ ζ (ι F))) → IsUnit (R.ρ s F) := by
      intro F hF
      exact (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s F)).2).2 fun ζ => by
        rw [hρ s hs]
        exact hF ζ
    refine ⟨hcomp X fun ζ => ?_, fun s' hs' hne => hcomp _ fun ζ => ?_⟩
    · rw [G1, map_mul, map_pow]
      refine (w.isUnit.map (ρζ ζ)).mul (IsUnit.pow _ ?_)
      rw [isUnit_iff_constantCoeff]
      have h := congrArg constantCoeff (hρζ s hs (ζ : LL) ζ.2)
      simp only [map_add, map_one, map_mul, constantCoeff_C, constantCoeff_exp, mul_one] at h
      rw [eq_sub_of_add_eq' h]
      exact (sub_ne_zero.2 ((hprim s ζ).ne_one (Nat.one_lt_pow (Nat.succ_ne_zero s) hp.one_lt))).isUnit
    · obtain ⟨w', hw'⟩ := hG s'
      rw [hw', map_mul, hcyc s hs]
      refine (w'.isUnit.map (ρζ ζ)).mul ?_
      rw [isUnit_iff_constantCoeff, LevelStatements.Lv.constantCoeff_aeval]
      simp only [map_mul, constantCoeff_C, constantCoeff_exp, mul_one]
      refine Ne.isUnit fun h0 => hne ?_
      have hroot : (Polynomial.cyclotomic (B.ℓ ^ (s' + 1)) LL).IsRoot (ζ : LL) := by
        rw [Polynomial.IsRoot.def, ← Polynomial.coe_aeval_eq_eval]
        exact h0
      have h := ((Polynomial.isRoot_cyclotomic_iff_charZero (hpos s')).1 hroot).unique (hprim s ζ)
      exact Nat.succ_injective (Nat.pow_right_injective hp.two_le h)

  have hComplR : R.Compl ϖ := by
    intro s hs k a hk
    obtain ⟨ζ, hζ⟩ := hroot
    have hζ0 : IsPrimitiveRoot (ζ ^ (B.ℓ ^ (n0 - (s + 1)))) (B.ℓ ^ (s + 1)) :=
      hζ.pow (pow_pos hp.pos _) (by rw [← pow_add]; congr 1; omega)
    have hcd := hCompl O LL B.ℓ s hp hℓm ⟨_, hζ0⟩ ρζ
      (fun ζ' hζ' => hρζ s hs ζ' ((mem_primitiveRoots (hpos s)).2 hζ')) k (ι a)
      (fun ζ' hζ' => by
        have h := (((hPi LL ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)).2 (R.ρ s a)).1 k).1 hk
          ⟨ζ', (mem_primitiveRoots (hpos s)).2 hζ'⟩
        rwa [hρ s hs] at h)
    obtain ⟨w', hw'⟩ := hG s
    have hdv : ι (B.p s ^ k) ∣ ι a := by
      rw [map_pow, hw', mul_pow, ← Units.val_pow_eq_pow_val, Units.mul_left_dvd]
      exact hcd
    obtain ⟨z, hz⟩ := (hDesc O ι (B.ℓ - 1) hl1 ⟨w, G1⟩).2 _ _ hdv
    exact ⟨0, z, by rw [pow_zero, map_one, one_mul]; exact hz⟩

  have hunitu : ∀ s, IsUnit (PadicInt.toZModPow (s + 1) uZ) := fun s =>
    IsUnit.of_pow_eq_one (pow_orderOf_eq_one _)
      (by rw [LevelStatements.Ln03.orderOf_u hℓ2 uZ huZ s]; exact (pow_pos hp.pos _).ne')
  have hunitom : ∀ s j, IsUnit (PadicInt.toZModPow (s + 1) (om j)) := fun s j =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, hom j, map_one]) hl1.ne'
  have hmem : ∀ s (a : ZMod (B.ℓ ^ (s + 1))), IsUnit a →
      ∀ ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ : LL) ^ a.val ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL := fun s a ha ζ =>
    pow_val_mem_primitiveRoots _ (hpos s) a ha ζ.2
  have hsig : ∀ s < ell, ∀ (x : Ks LL B.ℓ s) (k : ℕ) (ζ : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)),
      ∃ ζ' : ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL),
        (ζ' : LL) = (ζ : LL) ^ ((PadicInt.toZModPow (s + 1) uZ).val ^ k) ∧
          (⇑(R.lev s).σ)^[k] x ζ = x ζ' := by
    intro s hs x k
    induction k with
    | zero => intro ζ; exact ⟨ζ, by simp, rfl⟩
    | succ k ih =>
      intro ζ
      obtain ⟨ζ2, h2, h2'⟩ := ih ⟨_, hmem s _ (hunitu s) ζ⟩
      refine ⟨ζ2, ?_, ?_⟩
      · rw [h2]
        change ((ζ : LL) ^ _) ^ _ = _
        rw [← pow_mul, ← pow_succ']
      · rw [Function.iterate_succ_apply', hσ s hs _ ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl, h2']

  have hK1c : ∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s := by
    intro s hs
    refine ⟨fun x => ?_, fun x hxσ hxτ => ?_⟩
    · funext ζ
      obtain ⟨ζ', h1, h2⟩ := hsig s hs x (B.ℓ ^ s) ζ
      rw [h2]
      congr 1
      apply Subtype.ext
      rw [h1]
      exact (LevelStatements.Ln03.sigma_u_order hℓ2 s uZ huZ ζ.2 _).2 dvd_rfl
    · classical
      let f : LL → LL := fun y =>
        if h : y ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL then x ⟨y, h⟩ else 0
      have hfu : ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL,
          f (ξ ^ (PadicInt.toZModPow (s + 1) uZ).val) = f ξ := by
        intro ξ hξ
        have hm := hmem s _ (hunitu s) ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hσ s hs x ⟨ξ, hξ⟩ ⟨_, hm⟩ rfl
        rw [hxσ] at h
        exact h.symm
      have hfΔ : ∀ a : ZMod (B.ℓ ^ (s + 1)), a ^ (B.ℓ - 1) = 1 →
          ∀ ξ ∈ primitiveRoots (B.ℓ ^ (s + 1)) LL, f (ξ ^ a.val) = f ξ := by
        intro a ha ξ hξ
        obtain ⟨j, hj⟩ := exists_toZModPow_eq_of_pow_pred_eq_one om hom hom' s a ha
        have hm := hmem s a (IsUnit.of_pow_eq_one ha hl1.ne') ⟨ξ, hξ⟩
        simp only [f]
        rw [dif_pos hm, dif_pos hξ]
        have h := hτ s hs j x ⟨ξ, hξ⟩ ⟨_, hm⟩ (by rw [hj])
        rw [hxτ j] at h
        exact h.symm
      have hconst := LevelStatements.Ln03.invariants_const hℓ2 s uZ huZ f hfu hfΔ
      by_cases hne : Nonempty ↥(primitiveRoots (B.ℓ ^ (s + 1)) LL)
      · obtain ⟨ξ0⟩ := hne
        refine ⟨x ξ0, ?_⟩
        funext ζ
        have h := hconst ξ0 ξ0.2 ζ ζ.2
        simp only [f, dif_pos ξ0.2, dif_pos ζ.2] at h
        simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        exact h
      · refine ⟨0, ?_⟩
        funext ζ
        exact absurd ⟨ζ⟩ hne

  have hK1d : ∀ s < ell, (R.lev s).PhiGammaCommute := by
    intro s hs j x
    funext ζ
    have e1 := hσ s hs ((R.lev s).τ j x) ζ ⟨_, hmem s _ (hunitu s) ζ⟩ rfl
    have e2 := hτ s hs j x ⟨_, hmem s _ (hunitu s) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩ rfl
    have e3 := hτ s hs j ((R.lev s).σ x) ζ ⟨_, hmem s _ (hunitom s j) ζ⟩ rfl
    have e4 := hσ s hs x ⟨_, hmem s _ (hunitom s j) ζ⟩
      ⟨_, hmem s _ (hunitom s j) ⟨_, hmem s _ (hunitu s) ζ⟩⟩
      (by
        change ((ζ : LL) ^ _) ^ _ = ((ζ : LL) ^ _) ^ _
        rw [← pow_mul, ← pow_mul, mul_comm])
    rw [e1, e2, e3, e4]
  exact ⟨hK1b, fun s hs => hu s hs, fun s hs => ⟨hK1c s hs, hK1d s hs⟩, hUnits, hComplR⟩

end LevelStatements.Link
end
end
