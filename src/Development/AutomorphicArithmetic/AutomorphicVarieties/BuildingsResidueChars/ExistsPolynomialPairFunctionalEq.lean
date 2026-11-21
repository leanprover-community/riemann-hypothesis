import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FunctionalEquationFromContinuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerLLocPolyNeZeroFarRight

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.T.GamFac

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem lt_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x < 1 ↔ 1 ≤ ord x := by
  have h := mem_valBall_iff_le_ord (n := 1) hx
  rwa [mem_valBall_one_iff] at h

private theorem le_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x ≤ 1 ↔ 0 ≤ ord x := by
  have h := mem_valBall_iff_le_ord (n := 0) hx
  rwa [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h

private theorem val_eq_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x = 1 ↔ ord x = 0 := by
  constructor
  · intro h
    have h1 := (le_one_iff hx).1 h.le
    have h2 : ¬ 1 ≤ ord x := fun h3 => absurd ((lt_one_iff hx).2 h3) (by rw [h]; exact lt_irrefl _)
    omega
  · intro h
    refine le_antisymm ((le_one_iff hx).2 h.ge) (not_lt.1 fun h3 => ?_)
    have := (lt_one_iff hx).1 h3
    omega

private theorem unram_iff (μ : kˣ →* ℂˣ) : IsUnram μ ↔ IsUnramifiedChar μ := by
  rw [isUnramifiedChar_iff]
  exact ⟨fun h u hu => h u ((val_eq_one_iff u.ne_zero).2 hu), fun h u hu => h u ((val_eq_one_iff u.ne_zero).1 hu)⟩

private theorem ord_unif_eq : ord ((UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k : kˣ) : k) = 1 := by
  obtain ⟨h1, h2⟩ := (polFacts k).1
  have a := (lt_one_iff (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k).ne_zero).1 h1
  have b := h2 _ ((lt_one_iff (unifUnit k).ne_zero).2 ord_unifUnit.ge)
  have c : ValuativeRel.valuation k ((unifUnit k * (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ b zero_le'
  have d := (le_one_iff (Units.ne_zero _)).1 c
  rw [ord_units_mul, ord_units_inv, ord_unifUnit] at d
  omega

end Loc

private theorem alg (a A q X : ℂ) (n : ℤ) (hA : A ≠ 0) (hq : q ≠ 0) (hX : X ≠ 0) :
    a * X ^ n * (1 - A⁻¹ * (q * X)⁻¹)⁻¹ / (1 - A * X)⁻¹ =
      -(A * q * a) * X ^ (n + 1) * (1 - A * X) / (1 - A * (q * X)) := by
  have hy : A * (q * X) ≠ 0 := mul_ne_zero hA (mul_ne_zero hq hX)
  have e : (1 - A⁻¹ * (q * X)⁻¹)⁻¹ = -(A * (q * X)) / (1 - A * (q * X)) := by
    rw [← mul_inv]
    by_cases h : A * (q * X) = 1
    · simp [h]
    · have h' : 1 - A * (q * X) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      have h'' : 1 - (A * (q * X))⁻¹ ≠ 0 := by
        intro h3
        apply h
        have := sub_eq_zero.1 h3
        rw [eq_comm, inv_eq_one] at this
        exact this
      rw [eq_div_iff h', inv_mul_eq_div, div_eq_iff h'']
      field_simp
      ring
  rw [e, zpow_add_one₀ hX, div_inv_eq_mul]
  ring

private theorem zpow_qpow (n : ℕ) (hn : 1 < n) (m : ℤ) (s : ℂ) :
    ((n : ℂ) ^ (-s)) ^ m = Complex.exp (((-(m * Real.log n) : ℝ) : ℂ) * s) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

end UpperTheory.V.T.GamFac

open UpperTheory.V.T.GamFac in
theorem UpperTheory.local_gamma_factor_exponential_form :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
        (ψ : AddChar F Circle) (μ : Fˣ →* ℂˣ), Continuous μ →
        ∃ (c : ℂ) (t : ℝ), ∀ s : ℂ, Ad3.gam ψ μ s = fac c t (residueCard F : ℝ) (lin μ) s := by
  intro F _ _ _ _ _ _ ψ μ _
  obtain ⟨a, n, hε⟩ := exists_localEpsilon_eq_mul_zpow (χ := μ) (ψ := ψ)
  have hq1 : 1 < residueCard F := one_lt_residueCard
  have hq0 : (residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  by_cases h : IsUnram μ
  · have hu := (unram_iff μ).1 h
    have hu' : IsUnramifiedChar μ⁻¹ := isUnramifiedChar_iff.2 fun u hu2 => by
      rw [MonoidHom.inv_apply, isUnramifiedChar_iff.1 hu u hu2, inv_one]
    have hval : μ (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif F) = μ (unifUnit F) :=
      quasiChar_apply_eq_of_isUnramified hu ord_unif_eq
    set A : ℂ := ((μ (unifUnit F) : ℂˣ) : ℂ) with hA
    have hA0 : A ≠ 0 := Units.ne_zero _
    refine ⟨-(A * (residueCard F : ℂ) * a), -((n + 1 : ℤ) * Real.log (residueCard F)), fun s => ?_⟩
    have hX : (residueCard F : ℂ) ^ (-s) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq0]
      exact Complex.exp_ne_zero _
    have e1 : (residueCard F : ℂ) ^ (1 - s) = (residueCard F : ℂ) * (residueCard F : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hq0, Complex.cpow_one]
    have e2 : (residueCard F : ℂ) ^ (-(1 - s)) = ((residueCard F : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
      rw [Complex.cpow_neg, e1]
    have e3 : ((μ⁻¹ (unifUnit F) : ℂˣ) : ℂ) = A⁻¹ := by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have e4 : lin μ = 1 - C A * X := by
      rw [lin, if_pos h, hval]
    rw [Ad3.gam, fac, hε s, localLFactor_of_isUnramified hu, localLFactor_of_isUnramified hu', e2, e3,
      Complex.ofReal_natCast, e4, alg _ _ _ _ _ hA0 hq0 hX, zpow_qpow _ hq1]
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, e1]
  · have hu : ¬ IsUnramifiedChar μ := fun h2 => h ((unram_iff μ).2 h2)
    have hu' : ¬ IsUnramifiedChar μ⁻¹ := fun h2 => hu (isUnramifiedChar_iff.2 fun u hu2 => by
      have := isUnramifiedChar_iff.1 h2 u hu2
      rwa [MonoidHom.inv_apply, inv_eq_one] at this)
    refine ⟨a, -(n * Real.log (residueCard F)), fun s => ?_⟩
    have e4 : lin μ = 1 := by rw [lin, if_neg h]
    rw [Ad3.gam, fac, hε s, localLFactor_of_not_isUnramified hu, localLFactor_of_not_isUnramified hu', e4,
      zpow_qpow _ hq1]
    simp
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_le_iff (x p : kˣ) :
    ValuativeRel.valuation k (x : k) ≤ ValuativeRel.valuation k (p : k) ↔ ord (p : k) ≤ ord (x : k) := by
  have h := mem_valBall_iff_le_ord (n := 0) (x * p⁻¹ : kˣ).ne_zero
  rw [mem_valBall_zero_iff, Valuation.mem_integer_iff, ord_units_mul, ord_units_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    mul_inv_le_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 p.ne_zero)), one_mul] at h
  rw [h]
  omega

private theorem val_lt_iff (x : kˣ) : ValuativeRel.valuation k (x : k) < 1 ↔ 1 ≤ ord (x : k) := by
  have h := mem_valBall_iff_le_ord (n := 1) x.ne_zero
  rwa [mem_valBall_one_iff] at h

private theorem ord_unif : ord ((UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k : kˣ) : k) = 1 := by
  have hex : ∃ p : kˣ, ValuativeRel.valuation k (p : k) < 1 ∧
      ∀ x : k, ValuativeRel.valuation k x < 1 → ValuativeRel.valuation k x ≤ ValuativeRel.valuation k (p : k) := by
    refine ⟨unifUnit k, (val_lt_iff _).2 ord_unifUnit.ge, fun x hx => ?_⟩
    by_cases h0 : x = 0
    · simp [h0]
    · have h1 := (val_lt_iff (Units.mk0 x h0)).1 hx
      exact (val_le_iff (Units.mk0 x h0) _).2 (by rw [ord_unifUnit]; exact h1)
  obtain ⟨h1, h2⟩ := Classical.epsilon_spec hex
  have a := (val_lt_iff _).1 h1
  have b := (val_le_iff _ _).1 (h2 _ ((val_lt_iff (unifUnit k)).2 ord_unifUnit.ge))
  rw [ord_unifUnit] at b
  exact le_antisymm b a

private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnramifiedChar a) (hb : IsUnramifiedChar b) :
    IsUnramifiedChar (a * b) :=
  isUnramifiedChar_iff.2 fun u hu => by
    rw [MonoidHom.mul_apply, isUnramifiedChar_iff.1 ha u hu, isUnramifiedChar_iff.1 hb u hu, one_mul]

private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnramifiedChar a) : IsUnramifiedChar a⁻¹ :=
  isUnramifiedChar_iff.2 fun u hu => by
    rw [MonoidHom.inv_apply, isUnramifiedChar_iff.1 ha u hu, inv_one]

private theorem local_l_factor_rank_three_unramified {ν c : kˣ →* ℂˣ} (hν : IsUnramifiedChar ν) (hc : IsUnramifiedChar c) (s : ℂ) :
    Ad3.lf3 ν c s = ((tri (ν (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k)) (c (unifUnit k))).map
      fun b => (1 - b * (residueCard k : ℂ) ^ (-s))⁻¹).prod := by
  rw [Ad3.lf3, localLFactor_of_isUnramified (unr_mul hν hc), localLFactor_of_isUnramified hc,
    localLFactor_of_isUnramified (unr_mul (unr_inv hν) hc), quasiChar_apply_eq_of_isUnramified hν ord_unif]
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_assoc]

end Loc

private theorem tri_inv (a x : ℂˣ) : (tri a x).map (·⁻¹) = tri a x⁻¹ := by
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Units.val_mul,
    Units.val_inv_eq_inv_val, mul_inv, inv_inv]
  rw [← Multiset.cons_zero, ← Multiset.cons_zero ((↑a)⁻¹ * (↑x)⁻¹ : ℂ), Multiset.cons_swap (((↑a)⁻¹ * (↑x)⁻¹ : ℂ)),
    Multiset.cons_swap (((↑a)⁻¹ * (↑x)⁻¹ : ℂ)), Multiset.cons_swap ((↑x)⁻¹ : ℂ)]

private theorem localChar_inv' (c : HeckeCharacter ℚ) (v : Ad3.Pl) : localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext x
  simp [GroundTheory.Automorphic.GodementSection.coe_localChar, HeckeCharacter.localComponent_apply,
    HeckeCharacter.toIdele_apply]
  exact Circle.coe_inv _

theorem UpperTheory.euler_product_adjoint_eq_standard :
    ∀ (D : Ad3.Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl), Ad3.admitted D c δ S → ∀ s : ℂ,
        Ad3.eul D c S s = eulerL ℚ (par D (toH c)) S s ∧ Ad3.eul D c⁻¹ S (1 - s) = eulerLd ℚ (par D (toH c)) S s := by
  intro D c δ S h s
  constructor
  · refine tprod_congr fun v => ?_
    have hν := D.unr v.1 fun hb => v.2 (h.bad hb)
    have hc := h.unr v.1 v.2
    refine (local_l_factor_rank_three_unramified hν hc s).trans ?_
    rw [GroundTheory.Global.residueCard_adicCompletion, ← Ad3P.DihedralUnramifiedPlaces.val_eq hc]
    rfl
  · refine tprod_congr fun v => ?_
    have hν := D.unr v.1 fun hb => v.2 (h.bad hb)
    have hc := h.unr v.1 v.2
    rw [localChar_inv']
    refine (local_l_factor_rank_three_unramified hν (unr_inv hc) (1 - s)).trans ?_
    rw [GroundTheory.Global.residueCard_adicCompletion, MonoidHom.inv_apply, ← Ad3P.DihedralUnramifiedPlaces.val_eq hc, ← tri_inv]
    rfl
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.euler_product_nonvanishing_right :
    ∀ (D : Ad3.Dat) (c : HeckeCharacter ℚ) (S : Set Ad3.Pl) (s : ℂ), 2 < s.re → eulerL ℚ (par D (toH c)) S s ≠ 0 := by
  intro D c S s hs
  have hx : ∀ p : Ad3.Pl, ‖(((toH c).val p : ℂˣ) : ℂ)‖ = 1 := by
    intro p
    have e : (toH c).val p = localChar c p (Formalism.L2.Host.atFin p (Formalism.L2.Host.unif p)) := rfl
    rw [e, GroundTheory.Automorphic.GodementSection.coe_localChar]
    exact Circle.norm_coe _
  have hn : ∀ p : Ad3.Pl, ‖((D.ν p (unif (p.adicCompletion ℚ)) : ℂˣ) : ℂ)‖ = 1 := fun p => (D.unit p).2 _
  refine (eulerL_locPoly_ne_zero_far_right ℚ 3 S
    (fun p => ({D.ν p (unif (p.adicCompletion ℚ)) * (toH c).val p, (toH c).val p,
      (D.ν p (unif (p.adicCompletion ℚ)))⁻¹ * (toH c).val p} : Multiset ℂˣ)) 0 (fun w _ => rfl) ?_ s
    (by simpa using hs)).1
  intro w _ b hb
  rw [Real.rpow_zero]
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl
  · rw [Units.val_mul, norm_mul, hn, hx, one_mul]
  · rw [hx]
  · rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hn, hx, inv_one, one_mul]
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem fac_mul (c c' : ℂ) (t t' q : ℝ) (P P' : ℂ[X]) (s : ℂ) :
    fac c t q P s * fac c' t' q P' s = fac (c * c') (t + t') q (P * P') s := by
  simp only [fac, eval_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [div_mul_div_comm]
  congr 1
  ring

private theorem fac_one (c : ℂ) (t q q' : ℝ) (s : ℂ) : fac c t q 1 s = fac c t q' 1 s := by
  simp only [fac, eval_one]

private def IsFac (f : ℂ → ℂ) (q : ℝ) (P : ℂ[X]) : Prop := ∃ (c : ℂ) (t : ℝ), ∀ s : ℂ, f s = fac c t q P s

private theorem IsFac.mul {f g : ℂ → ℂ} {q : ℝ} {P Q : ℂ[X]} (hf : IsFac f q P) (hg : IsFac g q Q) :
    IsFac (fun s => f s * g s) q (P * Q) := by
  obtain ⟨c, t, h⟩ := hf
  obtain ⟨c', t', h'⟩ := hg
  exact ⟨c * c', t + t', fun s => by rw [← fac_mul, ← h, ← h']⟩

private theorem IsFac.one {f : ℂ → ℂ} {q : ℝ} (q' : ℝ) (hf : IsFac f q 1) : IsFac f q' 1 := by
  obtain ⟨c, t, h⟩ := hf
  exact ⟨c, t, fun s => (h s).trans (fac_one c t q q' s)⟩

private theorem isFac_prod_one {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (q : ℝ) (h : ∀ u ∈ S, IsFac (f u) q 1) :
    IsFac (fun s => ∏ u ∈ S, f u s) q 1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 0, fun s => by simp [fac]⟩
  | insert a S ha ih =>
    have h1 := (h a (Finset.mem_insert_self _ _)).mul (ih fun u hu => h u (Finset.mem_insert_of_mem hu))
    rw [mul_one] at h1
    simpa only [Finset.prod_insert ha] using h1

private theorem isFac_prod {ι : Type} (S : Finset ι) (v : ι) (hv : v ∈ S) (f : ι → ℂ → ℂ) (q : ℝ) (P : ℂ[X])
    (h0 : IsFac (f v) q P) (h : ∀ u ∈ S, u ≠ v → IsFac (f u) q 1) : IsFac (fun s => ∏ u ∈ S, f u s) q P := by
  have h1 := h0.mul (isFac_prod_one (S.erase v) f q fun u hu => h u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu))
  rw [mul_one] at h1
  obtain ⟨c, t, h1⟩ := h1
  exact ⟨c, t, fun s => by rw [← h1 s]; exact (Finset.mul_prod_erase S (fun u => f u s) hv).symm⟩

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem unit_mul {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (h' : Ad3.IsUnit1 c) : Ad3.IsUnit1 (ν * c) :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h.2, h'.2, mul_one]⟩

private theorem unit_inv {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) : Ad3.IsUnit1 ν⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]⟩

private theorem lin_ne {ν : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (x : ℂ) (hx : 1 < ‖x‖) : (lin ν).eval x ≠ 0 := by
  unfold lin
  split_ifs
  · simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
    intro h0
    have h1 := congrArg norm (sub_eq_zero.1 h0)
    rw [norm_one, norm_mul, h.2, one_mul] at h1
    linarith
  · simp

private theorem local_linear_factor_ne_zero {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν) (h' : Ad3.IsUnit1 c) (x : ℂ) (hx : 1 < ‖x‖) :
    (lin3 ν c).eval x ≠ 0 := by
  simp only [lin3, eval_mul]
  exact mul_ne_zero (mul_ne_zero (lin_ne (unit_mul h h') x hx) (lin_ne h' x hx)) (lin_ne (unit_mul (unit_inv h) h') x hx)

private theorem local_linear_factor_ramified {ν c : Fˣ →* ℂˣ} (h : Ram3 ν c) : lin3 ν c = 1 := by
  simp only [lin3, lin, if_neg h.1, if_neg h.2.1, if_neg h.2.2, mul_one]

private theorem gamma_factor_rank_three_form [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) {ν c : Fˣ →* ℂˣ} (h : Ad3.IsUnit1 ν)
    (h' : Ad3.IsUnit1 c) : IsFac (Ad3.gam3 ψ ν c) (residueCard F : ℝ) (lin3 ν c) :=
  IsFac.mul (f := fun s => Ad3.gam ψ (ν * c) s * Ad3.gam ψ c s)
    (IsFac.mul (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul h h').1) (UpperTheory.local_gamma_factor_exponential_form F ψ _ h'.1))
    (UpperTheory.local_gamma_factor_exponential_form F ψ _ (unit_mul (unit_inv h) h').1)

end Loc

private theorem lR_ne (k : ℕ) (hk : 3 ≤ k) (δ : Bool) (s : ℂ) (hs : 0 < s.re) : Ad3.lR k δ s ≠ 0 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  refine mul_ne_zero ?_ (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
  · rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
    · rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h, -⟩
      simp at h
    · simp
      linarith
  · cases δ <;> simp <;> linarith

private theorem arch_eq (k : ℕ) (δ : Bool) (s : ℂ) : arch k s = Ad3.lR k δ s * Ad3.lR k (!δ) s := by
  cases δ
  · exact mul_comm _ _
  · rfl

private theorem gamR_pair (k : ℕ) (hk : 3 ≤ k) (δ : Bool) : ∃ g : ℂ, ∀ s : ℂ, 0 < s.re →
    Ad3.gamR k δ s * Ad3.gamR k (!δ) s * arch k s = g * arch k (1 - s) := by
  refine ⟨(-Complex.I) ^ (2 * k - if δ then 1 else 0) * (-Complex.I) ^ (2 * k - if (!δ) then 1 else 0), fun s hs => ?_⟩
  have h1 := lR_ne k hk δ s hs
  have h2 := lR_ne k hk (!δ) s hs
  rw [arch_eq k δ, arch_eq k δ, Ad3.gamR, Ad3.gamR]
  field_simp

private theorem loc_unit (c : HeckeCharacter ℚ) (v : Ad3.Pl) : Ad3.IsUnit1 (localChar c v) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c v, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar, Circle.norm_coe]⟩

private theorem loc_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (v : Ad3.Pl) :
    IsFac (Ad3.gam3 (localAdelicChar ℚ v) (D.ν v) (localChar c v)) (Ideal.absNorm v.asIdeal : ℝ) (lin3 (D.ν v) (localChar c v)) := by
  have h := gamma_factor_rank_three_form (localAdelicChar ℚ v) (D.unit v) (loc_unit c v)
  rwa [residueCard_adicCompletion] at h

private theorem fin_fac (D : Ad3.Dat) (c : HeckeCharacter ℚ) (S : Finset Ad3.Pl) (v : Ad3.Pl) (hv : v ∈ S)
    (h : ∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c u)) :
    IsFac (fun s => ∏ u ∈ S, Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u) s) (Ideal.absNorm v.asIdeal : ℝ)
      (lin3 (D.ν v) (localChar c v)) :=
  isFac_prod S v hv (fun u => Ad3.gam3 (localAdelicChar ℚ u) (D.ν u) (localChar c u)) _ _ (loc_fac D c v) fun u hu huv => by
    have h1 := loc_fac D c u
    rw [local_linear_factor_ramified (h u hu huv)] at h1
    exact h1.one _

private theorem eul_ne (D : Ad3.Dat) (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl) (h : Ad3.admitted D c δ S) :
    Ad3.eul D c S 3 ≠ 0 := by
  rw [(UpperTheory.euler_product_adjoint_eq_standard D c δ S h 3).1]
  exact UpperTheory.euler_product_nonvanishing_right D c S 3 (by norm_num)

theorem UpperTheory.exists_polynomial_pair_functional_eq :
    ∀ D : Ad3.Dat, Ad3.An D → ∀ (c₁ c₂ : HeckeCharacter ℚ) (δ : Bool) (S : Finset Ad3.Pl) (v : Ad3.Pl),
        Ad3.admitted D c₁ δ S → Ad3.admitted D c₂ (!δ) S → v ∈ S →
        (∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c₁ u) ∧ Ram3 (D.ν u) (localChar c₂ u)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (fun s => Ad3.eul D c₁ S s * Ad3.eul D c₂ S s)
          (fun s => Ad3.eul D c₁⁻¹ S (1 - s) * Ad3.eul D c₂⁻¹ S (1 - s)) β (Ideal.absNorm v.asIdeal : ℝ)
          (lin3 (D.ν v) (localChar c₁ v) * lin3 (D.ν v) (localChar c₂ v)) := by
  intro D hD c₁ c₂ δ S v h₁ h₂ hv hr
  obtain ⟨Λ₁, Λ₁', a₁, b₁, e₁⟩ := hD c₁ δ S h₁
  obtain ⟨Λ₂, Λ₂', a₂, b₂, e₂⟩ := hD c₂ (!δ) S h₂
  obtain ⟨g, hg⟩ := gamR_pair D.k D.three δ
  obtain ⟨c₀, t, hf⟩ := (fin_fac D c₁ S v hv fun u hu h => (hr u hu h).1).mul (fin_fac D c₂ S v hv fun u hu h => (hr u hu h).2)
  refine UpperTheory.functional_equation_from_continuation D.k _ _ (fun s => Λ₁ s * Λ₂ s) (fun s => Λ₁' s * Λ₂' s) g c₀ t _ _ D.three
    (by exact_mod_cast one_lt_absNorm_asIdeal v) (a₁.1.mul a₂.1) (b₁.1.mul b₂.1) (fun s hs => ?_) (fun s hs => ?_)
    ⟨3, by norm_num, mul_ne_zero (eul_ne D c₁ δ S h₁) (eul_ne D c₂ _ S h₂)⟩ (fun x hx => ?_) (fun s hs hs' => ?_)
  · simp only [a₁.2.2 s hs, a₂.2.2 s hs, pow_zero, one_mul]
  · have h : 1 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    simp only [b₁.2.2 _ h, b₂.2.2 _ h, pow_zero, one_mul]
  · rw [eval_mul]
    exact mul_ne_zero (local_linear_factor_ne_zero (D.unit v) (loc_unit c₁ v) x hx) (local_linear_factor_ne_zero (D.unit v) (loc_unit c₂ v) x hx)
  · rw [← hf s, ← hg s (by linarith)]
    simp only [e₁ s hs hs', e₂ s hs hs', Ad3.gamS]
    ring
end
