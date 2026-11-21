import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OfEMulStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ClsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatFormM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompactTorusUnitsEqTopOfNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EvenValuationNormCompactUnitsOfSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FinsumQuotientNormsOfNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.UnitAdd

section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.pStable :
    UpperTheory.V.Z.Sym.Loc.PStable := by
  intro O K _ _ _ _ _ Δ τ L hr j χ hj hχ a ha
  haveI := L.frac
  have hnω : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha, QuadraticAlgebra.norm_def]
    simp
  have hR : gOrb O j χ a = ((PS.Fv O τ).ncard : ℂ) := by
    rw [gLat O K Δ τ L hr j χ hj hχ a 1 1 (by rw [hnω]; simp), ← PS.vcount_eq L hr]
    simp [ha]
  rw [hR]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  set p : Kˣ := Units.mk0 _ hp0 with hpdef
  have hpv : ((p : Kˣ) : K) = algebraMap O K π := rfl
  have hpe : ¬ EvenVal O ((p : Kˣ) : K) := by
    rw [hpv]
    exact PS.not_even_irr L hπ
  have hfv : ∀ t : Kˣ, (PS.Fv O τ).ncard = (PS.Gs O τ (↑t) 1).ncard + (PS.Gs O τ (↑(t * p)) 1).ncard :=
    fun t => PS.fv_card L hr t p hpe
  by_cases hD : IsSquare (τ ^ 2 - 4)
  · have hI := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hr hD
    have hall : ∀ x : Kˣ, x ∈ NE τ := fun x =>
      (hsNE O K Δ τ L hr x).2 ((hsLaw O K Δ L).2.2.2 (τ ^ 2 - 4) x hr hD)
    obtain ⟨r, hrr⟩ := hD
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hr
      rw [hrr, mul_zero]
    have h2 : (2 : K) ≠ 0 := by
      have h := L.two.map (algebraMap O K)
      rw [map_ofNat] at h
      exact h.ne_zero
    set β : K := (τ - r) / 2 with hβdef
    set u : K := (((p : Kˣ) : K) - 1) / r with hudef
    have hb : β ^ 2 - τ * β + 1 = 0 := by
      rw [hβdef]
      field_simp
      linear_combination (-1 : K) * hrr
    have hτβ : τ - 2 * β = r := by
      rw [hβdef]
      field_simp
      ring
    have hru : r * u = ((p : Kˣ) : K) - 1 := by
      rw [hudef]
      field_simp
    set w : Etau K τ := ⟨1 - β * u, u⟩ with hwdef
    have hw : QuadraticAlgebra.norm w = ((p : Kˣ) : K) := by
      rw [QuadraticAlgebra.norm_def, hwdef]
      simp only
      linear_combination u ^ 2 * hb + u * hτβ + hru
    obtain ⟨y0, hy0⟩ : IsUnit w :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hw]; exact p.isUnit)
    have hy0n : QuadraticAlgebra.norm (y0 : Etau K τ) = ((p : Kˣ) : K) := by rw [hy0, hw]
    have hy0u : PS.nU y0 = p := Units.ext (by rw [PS.nU_val, hy0n])
    have hy0C : y0 ∉ Cint O τ := by
      intro h
      have := hI.1 y0 h
      rw [hy0n] at this
      exact hpe this
    have hpc : ∀ t : Kˣ, pcount O τ ↑t = ((PS.Fv O τ).ncard : ℂ) := by
      intro t
      have c1 : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = y0 * c * z ^ 2 := by
        intro y
        have hyne : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
          rw [← PS.nU_val]
          exact Units.ne_zero _
        rcases PS.even_or L hyne hp0 hpe with he | he
        · obtain ⟨z, c, hc, hyc⟩ := hI.2 y he
          exact ⟨z, c, hc, Or.inl (by rw [one_mul, hyc])⟩
        · have e : QuadraticAlgebra.norm ((y * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
              QuadraticAlgebra.norm (y : Etau K τ) / ((p : Kˣ) : K) := by
            rw [← PS.nU_val, map_mul, map_inv, hy0u, Units.val_mul, Units.val_inv_eq_inv_val,
              PS.nU_val, div_eq_mul_inv]
          obtain ⟨z, c, hc, hyc⟩ := hI.2 (y * y0⁻¹) (e ▸ he)
          refine ⟨z, c, hc, Or.inr ?_⟩
          rw [mul_assoc, ← hyc, mul_comm, inv_mul_cancel_right]
      have c2 : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * y0⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
        intro z hz
        exfalso
        have hE := hI.1 _ hz
        have hzn : ((PS.nU z : Kˣ) : K) ≠ 0 := Units.ne_zero _
        have e : QuadraticAlgebra.norm ((z ^ 2 * 1 * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
            ((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K) := by
          rw [← PS.nU_val, map_mul, map_mul, map_pow, map_one, mul_one, map_inv, hy0u, Units.val_mul,
            Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, div_eq_mul_inv]
        rw [e] at hE
        have hsq : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, (PS.nU z : K), hzn, by simp⟩
        apply hpe
        have := PS.even_mul hsq (PS.even_inv hE)
        have hp' : ((PS.nU z : Kˣ) : K) ^ 2 * (((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K))⁻¹ =
            ((p : Kˣ) : K) := by
          field_simp
        rwa [hp'] at this
      rw [PS.pcount_eq L hr t 1 y0 c1 c2]
      have hdisj : Disjoint (PS.Gs O τ (↑t) 1) (PS.Gs O τ (↑t) y0) := by
        rw [Set.disjoint_left]
        rintro S ⟨-, c, hc, hg⟩ ⟨-, c', hc', hg'⟩
        have hu := PS.gen_uniq hg hg'
        apply hy0C
        have e : y0 = (1 * c) * ((1 * c)⁻¹ * (y0 * c')) * c'⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (by rw [one_mul]; exact hc) hu) (inv_mem hc')
      rw [Set.ncard_union_eq hdisj (PS.gs_fin L hr t 1) (PS.gs_fin L hr t y0), PS.gs_ncard ((t : Kˣ) : K) y0,
        hy0u, hfv t, Units.val_mul]
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : Kˣ ⧸ NE τ), hpc]
    intro t ht
    exfalso
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ht (QuotientGroup.eq.2 (hall _))
  · have hC := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hr hD
    have hpc : ∀ (t : Kˣ) (b : (Etau K τ)ˣ), pcount O τ ↑t = ((PS.Gs O τ (↑t) b).ncard : ℂ) := by
      intro t b
      rw [PS.pcount_eq L hr t b b (fun y => ⟨1, b⁻¹ * y, by rw [hC]; trivial, Or.inl (by group)⟩)
        (fun z _ => by rw [hC]; trivial), Set.union_self]
    have hinv : ∀ t ∈ NE τ, ∀ x : Kˣ, pcount O τ ↑(t * x) = pcount O τ ↑x := by
      rintro t ⟨b, rfl⟩ x
      rw [hpc x b, PS.gs_ncard, hpc _ 1, Units.val_mul, mul_comm]
      rfl
    obtain ⟨⟨g0, hg0⟩, hsum⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hr hD
    have e : ∀ t : Kˣ, ((PS.Fv O τ).ncard : ℂ) = pcount O τ ↑t + pcount O τ ↑(t * p) := by
      intro t
      rw [hfv t, Nat.cast_add, hpc t 1, hpc (t * p) 1]
    by_cases hpN : p ∈ NE τ
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑g0 :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv g0 hg0
      rw [hS]
      have e1 := e 1
      have e2 := e g0
      rw [mul_comm, hinv p hpN] at e1 e2
      linear_combination (-1 / 2 : ℂ) * e1 + (-1 / 2 : ℂ) * e2
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑p :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv p hpN
      rw [hS, e 1, one_mul]
end

section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.stable : UpperTheory.V.Z.Sym.Loc.Stable := by
  unfold Stable
  intro O K _ _ _ _ _ Δ τ hL c d m hD hev j hj χ hχ a ha
  have hreg := hD.reg
  have hc := hD.c_ne
  have h2K : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hshift : ∀ (f : Kˣ → ℂ), (∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x) → ∀ g : Kˣ,
      (∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)) → stabSum O c d m = ∑ᶠ t : Kˣ ⧸ NE τ, f (Quotient.out t) := by
    intro f hf g hk
    unfold stabSum
    rw [finsum_congr (fun t => hk _)]
    exact (sumShift O K Δ τ hL hreg f hf g).1
  by_cases hτ : τ ∈ (algebraMap O K).range
  swap
  · have h0 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0 := by
      intro t
      by_contra hne
      exact hτ (vanish O K Δ τ hL c d _ (datSmul K Δ τ c d m hD t) hne).1
    have hg : gOrb O j χ a = 0 := by
      by_contra hne
      exact hτ (gVanish O K Δ τ hL j hj χ a (Or.inl ha) hne)
    rw [hg]
    unfold stabSum
    simp only [h0, finsum_zero]
  obtain ⟨τ₀, hτ₀⟩ := hτ
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator hreg
  rcases tri hL τ₀ with ⟨hm, hu⟩ | ⟨hm, hu⟩ | ⟨hu1, hu2⟩
  · have hx : (2 + τ₀) - 2 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      have e : (2 + τ₀) - 2 ^ 2 = τ₀ - 2 := by ring
      rw [e]
      exact hm
    obtain ⟨r, hr2, hrm⟩ := sqrtO O K Δ hL (2 + τ₀) 2 hL.two hx
    have hrK : (algebraMap O K) r ^ 2 = 2 + τ := by
      rw [← map_pow, hr2, map_add, map_ofNat, hτ₀]
    have hlam : QuadraticAlgebra.norm ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) = 2 + τ := by
      rw [QuadraticAlgebra.norm_algebraMap, hrK]
    have hD0 := datLam K Δ τ c hreg hc _ hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c _ hlam z hz m' hm'
    have hP := caseP O K Δ τ hL hreg r hrm hrK c hev j χ hj hχ a ha z hz
    let f : Kˣ → ℂ := fun y => lcount O c (dLam ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk]
    have hc2 : -2 * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2K) hc
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hP ⟨Units.mk0 _ hc2, by rw [Units.val_mk0]⟩).1
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hm2 : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) = τ₀ + 2 := by push_cast; ring
      rw [e]
      exact hm
    obtain ⟨x, y, _, hsq, hn⟩ := rootEx O K Δ τ hL τ₀ (-1) hτ₀ hm2
    set u : Etau K τ := { re := (algebraMap O K) x, im := (algebraMap O K) y } with hu_def
    have hu2' : u ^ 2 = -ω := by
      rw [hsq]
      push_cast
      ring
    obtain ⟨ν, hνI, hνN⟩ := normEx O K Δ hL (-1)
    have hνN' : QuadraticAlgebra.norm ν = -1 := by
      rw [hνN]
      simp
    obtain ⟨ε, s, hs0, hΔ⟩ := hL.even
    have hΔ' : Δ * (s⁻¹) ^ 2 = (algebraMap O K) ↑ε := by
      rw [hΔ]
      field_simp
    obtain ⟨hdn, hform⟩ := datFormM O K Δ τ hL c u hu2' hn ν hνN' s⁻¹ (inv_ne_zero hs0)
    obtain ⟨m', hm'', hmove⟩ := dat_move hL hD hdn
    obtain ⟨t₁, rfl⟩ := hform m' hm''
    have hM := caseM O K Δ τ hL hreg τ₀ hτ₀ hm c hevc u hu2' hn ν hνI hνN' s⁻¹ ε hΔ'
    let g : Kˣ := t₁ * Units.mk0 _ hreg
    let f : Kˣ → ℂ := fun y => pcount O τ (y : K)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := by
      intro t ht x
      simp only [f, Units.val_mul]
      exact pNorm O K Δ τ hL t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g) := by
      intro k
      rw [hmove, ← smul_assoc, smul_smul, ← Units.val_mul, hM]
      simp only [f, g, Units.val_mul, Units.val_mk0, mul_assoc]
    rw [hshift f hf g hk]
    exact pStable O K Δ τ hL hreg j χ hj hχ a ha
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu2
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hU : (algebraMap O K) ↑(-(hu1.unit * hu2.unit)) = τ ^ 2 - 4 := by
      rw [Units.val_neg, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_neg, map_mul, map_add, map_sub,
        map_ofNat, hτ₀]
      ring
    obtain ⟨lam, hlamI, hlamN⟩ := normEx O K Δ hL hu1.unit
    have hlam : QuadraticAlgebra.norm lam = 2 + τ := by
      rw [hlamN, IsUnit.unit_spec, map_add, map_ofNat, hτ₀]
    have hD0 := datLam K Δ τ c hreg hc lam hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c lam hlam z hz m' hm'
    have hG := caseG O K Δ τ hL ⟨_, hU⟩ c hevc lam hlamI hlam z hz
    have hga := (gVals O K Δ τ hL hreg ⟨τ₀, hτ₀⟩ j χ hj hχ a ha z hz).2.1 ⟨_, hU⟩
    let f : Kˣ → ℂ := fun y => lcount O c (dLam lam z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk, hga]
    have h1 : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
      rw [Units.val_one]
      unfold hs
      rw [if_pos ⟨1, 0, by ring⟩]
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hG ⟨1, h1⟩).1
end
