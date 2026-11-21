import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OrdinaryFlagThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J

namespace UpperTheory.V.Z.Keep.OrdFlag2

open Matrix

private theorem tri_of_lines {k H : Type} [Field k] (T : H → Matrix (Fin 2) (Fin 2) k) (a b : H → k) (x y p q : k)
    (hx : x ≠ 0 ∨ y ≠ 0) (hp : p ≠ 0 ∨ q ≠ 0) (hpx : p * x + q * y = 0)
    (h0 : ∀ s, T s 0 0 * x + T s 0 1 * y = a s * x) (h1 : ∀ s, T s 1 0 * x + T s 1 1 * y = a s * y)
    (h2 : ∀ s, p * T s 0 0 + q * T s 1 0 = b s * p) (h3 : ∀ s, p * T s 0 1 + q * T s 1 1 = b s * q) :
    ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * T s * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = b s := by
  obtain ⟨u, v, huv⟩ : ∃ u v : k, u * x + v * y = 1 := by
    rcases hx with h | h
    · exact ⟨x⁻¹, 0, by field_simp; ring⟩
    · exact ⟨0, y⁻¹, by field_simp; ring⟩
  have hd : u * q - v * p ≠ 0 := fun e => by
    have e1 : q = (u * q - v * p) * x := by linear_combination (-q) * huv + v * hpx
    have e2 : p = -(u * q - v * p) * y := by linear_combination (-p) * huv + u * hpx
    rw [e, zero_mul] at e1
    rw [e, neg_zero, zero_mul] at e2
    rcases hp with h | h
    · exact h e2
    · exact h e1
  set d := u * q - v * p with hdd
  let Q0 : Matrix (Fin 2) (Fin 2) k := !![u, v; p, q]
  let Q1 : Matrix (Fin 2) (Fin 2) k := !![x, -v / d; y, u / d]
  have hQ : Q0 * Q1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination huv
    · field_simp; ring
    · linear_combination hpx
    · field_simp; rw [hdd]; ring
  let Q : GL (Fin 2) k := ⟨Q0, Q1, hQ, mul_eq_one_comm.1 hQ⟩
  refine ⟨Q, fun s => ?_⟩
  have e : ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Q1 := rfl
  have e' : (Q : Matrix (Fin 2) (Fin 2) k) = Q0 := rfl
  rw [e, e']
  have a0 := h0 s
  have a1 := h1 s
  have a2 := h2 s
  have a3 := h3 s
  refine ⟨?_, ?_, ?_⟩
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    linear_combination x * a2 + y * a3 + b s * hpx
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    linear_combination u * a0 + v * a1 + a s * huv
  · simp [Q0, Q1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    field_simp
    linear_combination (-v) * a2 + u * a3

end UpperTheory.V.Z.Keep.OrdFlag2

namespace UpperTheory.V.Z.Keep.OrdFlag2

open Matrix

private theorem flag_block {k H : Type} [Field k] (R : H → Matrix (Fin 3) (Fin 3) k) (a c : H → k) (g : GL (Fin 3) k)
    (hb : ∀ s, R s 0 1 = 0 ∧ R s 1 0 = 0 ∧ R s 1 2 = 0 ∧ R s 2 1 = 0 ∧ R s 1 1 = 1)
    (ht : ∀ s, ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 1 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 1 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 0 0 = a s ∧
      ((g : Matrix (Fin 3) (Fin 3) k) * R s * ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) 2 2 = c s)
    (s0 s2 : H) (h0 : a s0 ≠ 1) (h2 : c s2 ≠ 1) :
    ∃ Q : GL (Fin 2) k, ∀ s, ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 0 = 0 ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 0 0 = a s ∧
      ((Q : Matrix (Fin 2) (Fin 2) k) * corner (R s) * ((Q⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = c s := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3) (Fin 3) k, P = (g : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Matrix (Fin 3) (Fin 3) k, I = ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := ⟨_, rfl⟩
  have hPI : P * I = 1 := by rw [hP, hI, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hIP : I * P = 1 := by rw [hP, hI, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [← hP, ← hI] at ht
  have hcol : ∀ s i, (R s * I) i 0 = a s * I i 0 := fun s i => by
    obtain ⟨t1, t2, -, t4, -⟩ := ht s
    have e : R s * I = I * (P * R s * I) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hIP, Matrix.one_mul]
    rw [e, Matrix.mul_apply, Fin.sum_univ_three, t1, t2, t4]
    ring
  have hrow : ∀ s j, (P * R s) 2 j = c s * P 2 j := fun s j => by
    obtain ⟨-, t2, t3, -, t5⟩ := ht s
    have e : P * R s = (P * R s * I) * P := by
      rw [Matrix.mul_assoc _ I P, hIP, Matrix.mul_one]
    rw [e, Matrix.mul_apply, Fin.sum_univ_three, t2, t3, t5]
    ring
  have hz : I 1 0 = 0 := by
    have h := hcol s0 1
    obtain ⟨-, b2, b3, -, b5⟩ := hb s0
    rw [Matrix.mul_apply, Fin.sum_univ_three, b2, b3, b5] at h
    have h' : (a s0 - 1) * I 1 0 = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h0)
  have ht1 : P 2 1 = 0 := by
    have h := hrow s2 1
    obtain ⟨b1, -, -, b4, b5⟩ := hb s2
    rw [Matrix.mul_apply, Fin.sum_univ_three, b1, b4, b5] at h
    have h' : (c s2 - 1) * P 2 1 = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 h2)
  have e20 : P 2 0 * I 0 0 + P 2 2 * I 2 0 = 0 := by
    have h := congrFun (congrFun hPI 2) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_ne (by decide)] at h
    linear_combination h
  have e00 : P 0 0 * I 0 0 + P 0 2 * I 2 0 = 1 := by
    have h := congrFun (congrFun hPI 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz, Matrix.one_apply_eq] at h
    linear_combination h
  have e22 : P 2 0 * I 0 2 + P 2 2 * I 2 2 = 1 := by
    have h := congrFun (congrFun hPI 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1, Matrix.one_apply_eq] at h
    linear_combination h
  have hx : I 0 0 ≠ 0 ∨ I 2 0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at e00
    simp at e00
  have hp : P 2 0 ≠ 0 ∨ P 2 2 ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at e22
    simp at e22
  refine tri_of_lines (fun s => corner (R s)) a c (I 0 0) (I 2 0) (P 2 0) (P 2 2) hx hp e20 (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s => ?_)
  · have h := hcol s 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
    show R s 0 0 * I 0 0 + R s 0 2 * I 2 0 = _
    linear_combination h
  · have h := hcol s 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, hz] at h
    show R s 2 0 * I 0 0 + R s 2 2 * I 2 0 = _
    linear_combination h
  · have h := hrow s 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
    show P 2 0 * R s 0 0 + P 2 2 * R s 2 0 = _
    linear_combination h
  · have h := hrow s 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, ht1] at h
    show P 2 0 * R s 0 2 + P 2 2 * R s 2 2 = _
    linear_combination h

private theorem ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (A : ValuationSubring Ω) (hv : A.valuation (l : Ω) < 1) {M : ℕ} (hM : 1 ≤ M) (d : ℤ) (hd : d ≠ 0)
    (χ : G F Ω →* (Qbar l)ˣ) (hχ : Af.KillsMu M χ) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hI : ∀ s : ↥(Dec (F := F) A), (s : G F Ω) ∈ Ine (F := F) A → κ s = cycBar F Ω l s ^ d * χ s) :
    ∃ s, κ s ≠ 1 := by
  have hfin : Finite χ.range := (UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ hχ).to_subtype
  have hN : ∀ s, χ s ^ Nat.card χ.range = 1 := fun s =>
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, s, rfl⟩ : χ.range)))
  have hN0 : Nat.card χ.range ≠ 0 := Nat.card_pos.ne'
  obtain ⟨g, hg, hne⟩ := UpperTheory.V.Ws.Pt.cycIne F Ω l A hv (d * Nat.card χ.range)
    (mul_ne_zero hd (by exact_mod_cast hN0))
  refine ⟨⟨g, Ine_le_Dec A hg⟩, fun e => hne ?_⟩
  have h1 := hI ⟨g, Ine_le_Dec A hg⟩ hg
  rw [e] at h1
  have h2 : cycBar F Ω l g ^ d = (χ g)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
  rw [_root_.zpow_mul, h2, zpow_natCast, inv_pow, hN, inv_one]

end UpperTheory.V.Z.Keep.OrdFlag2

theorem UpperTheory.V.Z.Keep.ordFlag2 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → Block η r → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ W : G K Ω →* GL (Fin 2) (Qbar l), (∀ s, (W s).val = corner (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∃ A' : ValuationSubring Ω, IsPlaceOver A' w ∧ ∃ κ, Af.FlagAt N ![(e : ℤ), -(e : ℤ)] W A' κ := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ C₀ k hΦ A _ _ r hr hbl h11 K _ _ _ _ _ hK W hW w hw
  have hker : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ η.ker := fun s => by
    rw [hK, ← range_galEmb]
    exact ⟨s, rfl⟩
  let j : G K Ω →* η.ker := (galEmb ℚ K Ω).codRestrict _ hker
  let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart η (UnitaryThreeInertia.push A.val r) hr.red.mult).comp j
  have hρ : ∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat := fun s => rfl
  obtain ⟨A', hA, κ, χ, hχ, ⟨g, hg⟩, hI⟩ :=
    UpperTheory.V.Z.Keep.ordFlag3 Ω l c N e ψ η σ g₁ B M hL L Φ C₀ k hΦ A r hr K hK ρ hρ w hw
  have hv : A'.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hw
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have he : (e : ℤ) ≠ 0 := by
    have := hL.e_pos
    omega
  obtain ⟨s0, h0⟩ := OrdFlag2.ne_one A' hv hN (e : ℤ) he (χ 0) (hχ 0) (κ 0) (hI 0)
  obtain ⟨s2, h2⟩ := OrdFlag2.ne_one A' hv hN (-(e : ℤ)) (neg_ne_zero.2 he) (χ 2) (hχ 2) (κ 2) (hI 2)
  have hent : ∀ (s : G K Ω) (a b : Fin 3), Odd (wt a b) → (ρ s).val a b = 0 := fun s a b h => by
    rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, hbl _ (hker s) a b h]
    exact map_zero _
  have hmid : ∀ s : G K Ω, (ρ s).val 1 1 = 1 := fun s => by
    rw [hρ, UnitaryThreeInertia.push, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, h11 _ (hker s)]
    exact map_one _
  obtain ⟨Q, hQ⟩ := OrdFlag2.flag_block (fun s : ↥(Dec (F := K) A') => (ρ s.1).val)
    (fun s => ((κ 0 s : (Qbar l)ˣ) : Qbar l)) (fun s => ((κ 2 s : (Qbar l)ˣ) : Qbar l)) g
    (fun s => ⟨hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hent _ _ _ (by decide), hmid _⟩)
    (fun s => by
      obtain ⟨t1, t2⟩ := hg s
      exact ⟨t1 1 0 (by decide), t1 2 0 (by decide), t1 2 1 (by decide), t2 0, t2 2⟩)
    s0 s2 (fun e => h0 (Units.ext e)) (fun e => h2 (Units.ext e))
  refine ⟨A', hA, ![κ 0, κ 2], ![χ 0, χ 2], fun i => ?_, ⟨Q, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s hs => ?_⟩
  · fin_cases i
    · exact hχ 0
    · exact hχ 2
  · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      rw [Units.val_mul, Units.val_mul, hW, ← hρ]
    have hij' : i = 1 ∧ j = 0 := by
      revert hij; fin_cases i <;> fin_cases j <;> simp
    obtain ⟨rfl, rfl⟩ := hij'
    show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 0 = 0
    rw [e1]
    exact (hQ s).1
  · have e1 : (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val = (Q : Matrix (Fin 2) (Fin 2) (Qbar l)) * corner (ρ s.1).val * ((Q⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      rw [Units.val_mul, Units.val_mul, hW, ← hρ]
    fin_cases i
    · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 0 0 = _
      rw [e1]
      exact (hQ s).2.1
    · show (Q * W s.1 * Q⁻¹ : GL (Fin 2) (Qbar l)).val 1 1 = _
      rw [e1]
      exact (hQ s).2.2
  · fin_cases i
    · exact hI 0 s hs
    · exact hI 2 s hs
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem conj_into {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) :
    ∃ g : G F Ω, (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hmem : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hval : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hmem, ← hmem, map_eq_zero_iff _ g.injective]
  have hdec : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨g, hdec, fun s hs => ⟨hdec s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hval]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hmem y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem flag_at_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A B : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    (hB : IsPlaceOver B w) {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ κ' : Fin n → ↥(Dec (F := K) B) →* (Qbar l)ˣ, FlagAt M m (r.comp (res F Ω K)) B κ' := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hI⟩ := hκ
  obtain ⟨g, hD, hIn⟩ := conj_into w hA hB
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  have hcyc : ∀ (ψ : G F Ω →* (Qbar l)ˣ) (s : G K Ω), ψ (g * res F Ω K s * g⁻¹) = ψ (res F Ω K s) := fun ψ s => by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hrep : ∀ s : G K Ω, P * r g * r (res F Ω K s) * (P * r g)⁻¹ = P * r (g * res F Ω K s * g⁻¹) * P⁻¹ := fun s => by
    rw [map_mul, map_mul, map_inv]
    group
  refine ⟨fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs, ⟨P * r g, fun s => ?_⟩,
    fun i s hs => ?_⟩
  · rw [MonoidHom.comp_apply, hrep]
    exact hP (d s)
  · have h := hI i (d s) (hIn s hs)
    rw [hd, hcyc, hcyc] at h
    exact h

end

theorem UpperTheory.V.Z.Keep.keepsGap :
    ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ κ, Af.FlagAt M m r A κ) → (∀ i j, m i ≠ m j + 1) → Z.Win.Keeps r L := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r hM hflag hgap w hw _ B hB
  have hlow : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal := by
    change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨A, hA, κ, hκ⟩ := hflag _ hlow
  obtain ⟨κ', hκ'⟩ := flag_at_place w hA hB hκ
  have hfl : IsFlagOn _ _ κ' := hκ'.choose_spec.2.1
  exact ⟨κ', hfl, Lev.unlGap L Ω l n M hM m _ w hw B hB _ hκ' hgap⟩
end

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.Th UpperTheory.V.Z.J

private lemma weight_gap_ne_succ (e : ℕ) (i j : Fin 2) :
    (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≠ (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j + 1 := by
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem UpperTheory.V.Z.Keep.keeps2 :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), Pr.LinkHyp c N e η σ B M → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ) (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A), Pr.OrdPt l η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B r → Block η r → (∀ g ∈ η.ker, (r g).mat 1 1 = 1) → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω] [IsAlgClosure K Ω], η.ker = galOf ℚ K Ω → ∀ [Algebra K L] [IsScalarTower K L Ω] (W : G K Ω →* GL (Fin 2) (Qbar l)), (∀ s, (W s).val = corner (UnitaryThreeInertia.push A.val r (galEmb ℚ K Ω s)).mat) → Z.Win.Keeps W L :=
  fun Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ C₀ k hΦ A _ _ r hO hB h1 K _ _ _ _ _ hK _ _ W hW =>
    UpperTheory.V.Z.Keep.keepsGap K L Ω l 2 N ![(e : ℤ), -(e : ℤ)] W (NeZero.one_le)
      (UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₁ B M hL L Φ C₀ k hΦ A r hO hB h1 K hK W hW)
      (weight_gap_ne_succ e)
end
