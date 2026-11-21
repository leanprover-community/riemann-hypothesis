import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
import Development.DiscreteGroups.GlobalIrreducibility.DzLDepth
import Development.DiscreteGroups.GlobalIrreducibility.DzLTame
import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.DzGalUnr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
import Development.DiscreteGroups.GlobalIrreducibility.DzPinFinal
import Development.DiscreteGroups.GlobalIrreducibility.DzDigMain
import Development.DiscreteGroups.GlobalIrreducibility.DzKondo
import Development.DiscreteGroups.GlobalIrreducibility.DzFpMat
import GroundTheory.LocalFields.LocalFourierPadic
import Development.DiscreteGroups.GlobalIrreducibility.FixedNeBotOfEquiv
import Development.DiscreteGroups.GlobalIrreducibility.PhiTilde
import Development.DiscreteGroups.GlobalIrreducibility.LTw
import Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnitsStatement
import Development.DiscreteGroups.GlobalIrreducibility.DzFeDec
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil
import Development.DiscreteGroups.GlobalIrreducibility.DzGalEps

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem ine_restrict {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω} (t : Ine (F := E') A) :
    AlgEquiv.restrictScalars E (t : G E' Ω) ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => t.2.2 x hx⟩
  show AlgEquiv.restrictScalars E (t : G E' Ω) • A = A
  have hd : (t : G E' Ω) • A = A := t.2.1
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

theorem eq_trace_smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = (LinearMap.trace ℂ V f) • v := by
  obtain ⟨b, -, hspan⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c₀, hc₀⟩ := hspan (f b)
  have hf : f = c₀ • LinearMap.id := by
    ext w
    obtain ⟨c, rfl⟩ := hspan w
    rw [map_smul, ← hc₀, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  rw [hf, map_smul, LinearMap.trace_id, hV, Nat.cast_one, smul_eq_mul, mul_one, LinearMap.smul_apply,
    LinearMap.id_apply]

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) : M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_unique]

theorem tau_scalar (g : ℕ) [Fact g.Prime] (K : Type) [Field K] [Algebra (ZMod g) K] (θ : Kˣ →* ℂˣ)
    (τ : FDRep ℂ (Gn g 1))
    (hf : ∀ y : Gn g 1, Irreducible (y : Mt g 1).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g 1).charpoly = 0 →
        τ.character y = (-1) ^ (1 - 1) * ∑ j ∈ Finset.range 1, ((θ (z ^ g ^ j) : ℂˣ) : ℂ))
    (y : Gn g 1) (z : Kˣ) (hz : (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0)) (v : τ) :
    τ.ρ y v = ((θ z : ℂˣ) : ℂ) • v := by
  have key : ∀ (y : Gn g 1) (z : Kˣ), (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0) →
      τ.character y = ((θ z : ℂˣ) : ℂ) := fun y z hz => by
    have := hf y (by rw [charpoly_fin_one]; exact irreducible_X_sub_C _) z (by
      rw [charpoly_fin_one]; simp [hz])
    simpa using this
  have hdim : Module.finrank ℂ τ = 1 := by
    have h1 := key 1 1 (by simp)
    rw [FDRep.char_one, map_one, Units.val_one] at h1
    exact_mod_cast h1
  rw [eq_trace_smul_of_finrank_one hdim (τ.ρ y) v]
  congr 1
  exact key y z hz

theorem lOneOf : LOneOf := by
  intro HT E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hn1 hg hN a' ha' K _ _ red hr hk θ hθ τ
    hτ hf σ hs ξ hξ hξf
  subst hn1
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra (E := E)
  have hgp : g.Prime := Fact.out

  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar σ.smooth σ.irr
  have hωx : HasCentralChar (cls σ).rep ω := hasCentralChar_of_equiv (equivRep σ) hω

  have hωu : ∀ u : ℤ_[g]ˣ, ∀ U : (w.adicCompletion E)ˣ, (U : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      ∀ zc : Kˣ, (zc : K) = algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) → (ω U : ℂ) = θ zc := by
    intro u U hU zc hzc
    obtain ⟨φ, hφ0, hφ⟩ := hs
    obtain ⟨v0, hv0⟩ : ∃ v0, φ v0 ≠ 0 := by
      by_contra hc
      exact hφ0 (LinearMap.ext fun v => not_not.1 fun hne => hc ⟨v, hne⟩)
    let k : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u
    have h1 := hφ k v0
    have hred : ((GlobalTheory.GLp.red g 1 k : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
      simp [k, GlobalTheory.GLp.red]
    rw [tau_scalar g K θ τ hf _ zc (by rw [hred, hzc]), map_smul] at h1
    have e : Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k) = GeneralLinearGroup.scalar (Fin 1) U := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      fin_cases a; fin_cases b
      simp [k, GlobalTheory.GLp.inc, hU]
    have h2 : (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g 1 k) (φ v0) = (ω U : ℂ) • φ v0 := by
      show σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) (φ v0) = _
      rw [e, hω U]
    rw [h2] at h1
    exact (smul_left_injective ℂ hv0 h1).symm

  have hNw : normV w = g := by rw [← resCard_eq_normV w, DiscreteGroups.sglob.DzIso.resCard_eq i hi]
  have hN' : normV w' = g := by rw [hN, pow_one]
  have hgw' := natCast_mem_of_normV w' g 1 Nat.one_pos hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have hmap : ∀ y : 𝓞 E, y ∈ w.asIdeal → algebraMap (𝓞 E) (𝓞 E') y ∈ w'.asIdeal := fun y hy => by
    refine (h' _).1 ?_
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') y : 𝓞 E') : E') = algebraMap E Ω (y : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (y : E)).symm
    rw [e1]
    exact (h y).2 hy
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := fun hm => hg (by
    have hle : Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 hmap
    have h2 := Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hm
    rw [Ideal.map_pow] at h2
    have := Ideal.pow_right_mono hle 2 h2
    rwa [map_natCast] at this)

  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) (show 0 < g - 1 by have := hgp.two_le; omega)
  refine ⟨0, fun z => ?_⟩
  rw [pow_zero, pow_one]
  obtain ⟨t, x, hxz, hv⟩ := exists_ine_of_res g A w' h' 1 Nat.one_pos hN a' ha' K red hr hk z
  have hpol := hξf t x z hxz hv
  have htE := ine_restrict (E := E) t
  let s : Weil h := ineIncl h ⟨_, htE⟩
  rw [WD.inePol_of_mem_Ine _ htE] at hpol

  have hcard := WD.card_eig (rc (cls σ)) s
  rw [hL.dim] at hcard
  obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
  have hprod := hL.central (cls σ) ω hωx s
  rw [hα, Multiset.prod_singleton] at hprod
  rw [WD.charPol_eq_prod, hα] at hpol
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Finset.range_one, Finset.prod_singleton, pow_zero,
    pow_one] at hpol
  have hαξ : α = ((ξ z : ℂˣ) : ℂ) := by simpa using congrArg (Polynomial.eval 0) hpol
  have hξα : ((ξ z : ℂˣ) : ℂ) = α := hαξ.symm

  have hunit := GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha ⟨_, htE⟩
  have hu1 : ‖i.symm (a s : w.adicCompletion E)‖ = 1 := by
    have hv1 : Valued.v (a s : w.adicCompletion E) = 1 := hunit
    have hle := (DiscreteGroups.sglob.DzIso.v_le_iff i hi (i.symm (a s : w.adicCompletion E))).1 (by
      rw [RingEquiv.apply_symm_apply, hv1])
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have := (DiscreteGroups.sglob.DzIso.v_lt_iff i hi (i.symm (a s : w.adicCompletion E))).2 hlt
    rw [RingEquiv.apply_symm_apply, hv1] at this
    exact lt_irrefl _ this
  let u : ℤ_[g]ˣ := PadicInt.mkUnits hu1
  have hu : (a s : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) := by
    show _ = i (i.symm (a s : w.adicCompletion E))
    rw [RingEquiv.apply_symm_apply]

  obtain ⟨y, hy⟩ := GlobalTheory.unit_completion_approx_integer w (a s) hunit
  have hT' := HT E' Ω g A w' h' hgw' hg a' ha' π (by rw [hN']; exact hπ) t x hv
  have hT := HT E Ω g A w h hgw hgw2 a ha π (by rw [hNw]; exact hπ) ⟨_, htE⟩ y hy
  have hxy : A.valuation (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) < 1 := by
    have e : algebraMap E' Ω (x : E') - algebraMap E Ω (y : E) =
        ((t : G E' Ω) π / π - algebraMap E Ω (y : E)) - ((t : G E' Ω) π / π - algebraMap E' Ω (x : E')) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hT hT')
  set c : ZMod g := PadicInt.toZMod (u : ℤ_[g]) with hc
  have hym : y - (c.val : 𝓞 E) ∈ w.asIdeal := by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E)) < 1 := by
      have e : algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E) =
          -((a s : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) +
            i (((u : ℤ_[g]) : ℚ_[g]) - (c.val : ℚ_[g])) := by
        rw [map_sub, hu, map_natCast]
        push_cast
        ring
      rw [e]
      refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy) ?_
      refine (DiscreteGroups.sglob.DzIso.v_lt_iff i hi _).2 ?_
      have hk : (u : ℤ_[g]) - (c.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, hc, sub_self]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
        PadicInt.coe_sub, PadicInt.coe_natCast] at hk
      exact hk
    have h2 : w.valuation E ((y - (c.val : 𝓞 E) : 𝓞 E) : E) < 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w]
      exact h1
    exact (w.valuation_lt_one_iff_mem (K := E) _).1 h2
  have hA1 : A.valuation (algebraMap E Ω (y : E) - (c.val : Ω)) < 1 := by
    have := (h _).2 hym
    rw [show ((y - (c.val : 𝓞 E) : 𝓞 E) : E) = (y : E) - (c.val : E) by push_cast; ring, map_sub,
      map_natCast] at this
    exact this
  have hxm : x - (c.val : 𝓞 E') ∈ w'.asIdeal := by
    refine (h' _).1 ?_
    have e : algebraMap E' Ω ((x - (c.val : 𝓞 E') : 𝓞 E') : E') =
        (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) + (algebraMap E Ω (y : E) - (c.val : Ω)) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ hxy hA1
  have hzc : (z : K) = algebraMap (ZMod g) K c := by
    rw [← hxz]
    have := (RingHom.mem_ker.1 (hk ▸ hxm : x - (c.val : 𝓞 E') ∈ RingHom.ker red))
    rw [map_sub, map_natCast, sub_eq_zero] at this
    rw [this, ← map_natCast (algebraMap (ZMod g) K), ZMod.natCast_zmod_val]

  have hfin := hωu u (a s) hu z hzc
  refine Units.ext ?_
  rw [hξα, hprod]
  exact hfin

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k]

theorem eq_zero_of_eq_inv_mul {ψ : AddChar k Circle} {s : k} (hs : ψ s ≠ 1) {z : ℂ}
    (h : z = (((ψ s)⁻¹ : Circle) : ℂ) * z) : z = 0 := by
  have hc : ((ψ s)⁻¹ : Circle) ≠ 1 := by rwa [ne_eq, inv_eq_one]
  have hc' : (((ψ s)⁻¹ : Circle) : ℂ) ≠ 1 := fun h' => hc (Circle.ext (by rw [h', Circle.coe_one]))
  have h0 : ((((ψ s)⁻¹ : Circle) : ℂ) - 1) * z = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hc')

theorem vanish_perm {k' : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin (k' + 1)) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin (k' + 1)), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k (k' + 1), ∀ x, W (x * b) = W x)
    (π : Equiv.Perm (Fin (k' + 1))) (hπ : π ≠ 1) (b : GL (Fin (k' + 1)) k) (hb : b ∈ lowB k (k' + 1)) :
    W (GroundTheory.Automorphic.permGL k π * b) = 0 := by
  obtain ⟨i, hi⟩ := exists_descent π⁻¹ (inv_ne_one.2 hπ)
  obtain ⟨s, hs⟩ := AddChar.ne_one_iff.1 hψ
  have hne : i.succ ≠ i.castSucc := (ne_of_lt Fin.castSucc_lt_succ).symm
  have ha : (Pi.single i.castSucc s : Fin (k' + 1) → k) i.succ = 0 := by rw [Pi.single_apply, if_neg hne]
  have hemem : colElt (Pi.single i.castSucc s) i.succ ha ∈ unipB k (Fin (k' + 1)) := colElt_mem _ _ ha fun r hr => by
    rw [Pi.single_apply, if_neg (ne_of_gt (lt_trans Fin.castSucc_lt_succ hr))]
  have hesd : superDiag (colElt (Pi.single i.castSucc s) i.succ ha) = s := by
    rw [superDiag_colElt, Pi.single_eq_same]
  have hf : (GroundTheory.Automorphic.permGL k π)⁻¹ * colElt (Pi.single i.castSucc s) i.succ ha *
      GroundTheory.Automorphic.permGL k π ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply, colElt_apply, Matrix.one_apply_ne (π.injective.ne (ne_of_lt hrc))]
    by_cases hc : π c = i.succ
    · have hr : π r ≠ i.castSucc := by
        intro hr
        have h1' : π⁻¹ i.succ = c := by rw [← hc]; simp
        have h2' : π⁻¹ i.castSucc = r := by rw [← hr]; simp
        rw [h1', h2'] at hi
        exact absurd hrc (not_lt.2 hi.le)
      rw [if_pos hc, Pi.single_apply, if_neg hr, zero_add]
    · rw [if_neg hc, zero_add]
  have key : W (GroundTheory.Automorphic.permGL k π * b) =
      (((ψ s)⁻¹ : Circle) : ℂ) * W (GroundTheory.Automorphic.permGL k π * b) := by
    have e1 : colElt (Pi.single i.castSucc s) i.succ ha * (GroundTheory.Automorphic.permGL k π * b) =
        GroundTheory.Automorphic.permGL k π * (((GroundTheory.Automorphic.permGL k π)⁻¹ *
          colElt (Pi.single i.castSucc s) i.succ ha * GroundTheory.Automorphic.permGL k π) * b) := by group
    have := h1 _ hemem (GroundTheory.Automorphic.permGL k π * b)
    rw [hesd, e1, h2 _ (mul_mem hf hb), ← h2 b hb (GroundTheory.Automorphic.permGL k π)] at this
    exact this
  exact eq_zero_of_eq_inv_mul hs key

theorem supp {m : ℕ} (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (W : GL (Fin m) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin m), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k m, ∀ x, W (x * b) = W x) (x : GL (Fin m) k) (hx : W x ≠ 0) :
    ∃ u ∈ unipB k (Fin m), ∃ b ∈ lowB k m, x = u * b := by
  cases m with
  | zero => exact ⟨1, one_mem _, x, mem_lowB.2 fun i => i.elim0, (one_mul x).symm⟩
  | succ k' =>
  have hww : ∀ z, longElt (k' + 1) k * (longElt (k' + 1) k * z) = z := fun z => by
    rw [← mul_assoc, longElt_mul_self, one_mul]
  obtain ⟨σ, hσ⟩ := GroundTheory.Automorphic.exists_mem_doubleCoset_permGL (x * longElt (k' + 1) k)
  obtain ⟨b1, hb1, b2, hb2, he⟩ := DoubleCoset.mem_doubleCoset.1 hσ
  have hb2' : longElt (k' + 1) k * b2 * longElt (k' + 1) k ∈ lowB k (k' + 1) := by
    refine mem_lowB.2 fun i j hij => ?_
    rw [Units.val_mul, Units.val_mul, mul_longElt_apply, longElt_mul_apply]
    exact (GroundTheory.Automorphic.mem_borel_iff b2).1 hb2 _ _ (Fin.rev_lt_rev.2 hij)
  have hd : ∀ i, (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i ≠ 0 :=
    GroundTheory.Automorphic.borel_diag_ne_zero hb1
  let t : GL (Fin (k' + 1)) k := ⟨diagonal fun i => (b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i,
    diagonal fun i => ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) i i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hd i)⟩
  have hu : b1 * t⁻¹ ∈ unipB k (Fin (k' + 1)) := by
    refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i j = 0
      rw [mul_diagonal, (GroundTheory.Automorphic.mem_borel_iff b1).1 hb1 i j hji, zero_mul]
    · rw [Units.val_mul]
      show ((b1 : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k) * (diagonal _ : Matrix (Fin (k' + 1)) (Fin (k' + 1)) k)) i i = 1
      rw [mul_diagonal, mul_inv_cancel₀ (hd i)]
  have hPw : GroundTheory.Automorphic.permGL k σ * longElt (k' + 1) k = GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) := by
    rw [longElt_eq_permGL, map_mul]
  have ht : (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) ∈
      lowB k (k' + 1) := by
    refine mem_lowB.2 fun r c hrc => ?_
    rw [permConj_apply]
    exact diagonal_apply_ne _ ((σ * Fin.revPerm).injective.ne (ne_of_lt hrc))
  have hx' : x = b1 * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) * (longElt (k' + 1) k * b2 * longElt (k' + 1) k) := by
    calc x = x * longElt (k' + 1) k * longElt (k' + 1) k := by rw [mul_assoc, longElt_mul_self, mul_one]
    _ = b1 * GroundTheory.Automorphic.permGL k σ * b2 * longElt (k' + 1) k := by rw [he]
    _ = _ := by rw [← hPw]; simp only [mul_assoc, hww]
  have hx'' : x = (b1 * t⁻¹) * (GroundTheory.Automorphic.permGL k (σ * Fin.revPerm) *
      (((GroundTheory.Automorphic.permGL k (σ * Fin.revPerm))⁻¹ * t * GroundTheory.Automorphic.permGL k (σ * Fin.revPerm)) *
        (longElt (k' + 1) k * b2 * longElt (k' + 1) k))) := by
    rw [hx']; group
  by_cases hπ : σ * Fin.revPerm = 1
  · refine ⟨b1 * t⁻¹, hu, _, mul_mem ht hb2', ?_⟩
    rw [hx'', hπ, map_one, one_mul]
  · exfalso
    apply hx
    have h0 := vanish_perm ψ hψ W h1 h2 _ hπ _ (mul_mem ht hb2')
    rw [hx'', h1 _ hu, h0, mul_zero]

end DiscreteGroups.sglob.DzFp
end
end

section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_ne_zero_of_ne {l : Module.Dual ℂ V} (h0 : l ≠ 0) : ∃ v, l v ≠ 0 := by
  by_contra h
  push_neg at h
  exact h0 (LinearMap.ext h)

theorem chi_mul {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) {u u' : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    (hu' : u' ∈ unipB k (Fin n)) :
    (ψ (superDiag (u * u')) : ℂ) = ψ (superDiag u) * ψ (superDiag u') := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_ne h0
  have e1 := hl (u * u') (mul_mem hu hu') v
  rw [map_mul, Module.End.mul_apply, hl u hu, hl u' hu'] at e1
  have : ((ψ (superDiag (u * u')) : ℂ) - ψ (superDiag u) * ψ (superDiag u')) * l v = 0 := by
    rw [sub_mul, ← e1]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hv)

theorem exists_eigen [Fintype k] [DecidableEq k] {n : ℕ} {ψ : AddChar k Circle}
    {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) (h0 : l ≠ 0) :
    ∃ v, l v ≠ 0 ∧ ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v := by
  classical
  obtain ⟨v0, hv0⟩ := exists_ne_zero_of_ne h0
  refine ⟨∑ u : unipB k (Fin n), ((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0, ?_, fun u' hu' => ?_⟩
  · have hterm : ∀ u : unipB k (Fin n), l (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0) = l v0 := fun u => by
      rw [map_smul, hl _ u.2, smul_eq_mul, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    rw [map_sum]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨1⟩).ne') hv0
  · have hχ : ∀ w : unipB k (Fin n), (ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
        GL (Fin n) k)) : ℂ) = (ψ (superDiag u') : ℂ)⁻¹ * ψ (superDiag (w : GL (Fin n) k)) := fun w => by
      have := chi_mul hl h0 hu' (mul_mem (inv_mem hu') w.2)
      rw [mul_inv_cancel_left] at this
      rw [this, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
      rfl
    rw [map_sum, Finset.smul_sum]
    set a : unipB k (Fin n) := ⟨u', hu'⟩ with ha
    set F : unipB k (Fin n) → V := fun w =>
      ((ψ (superDiag ((a⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 with hF
    calc ∑ u : unipB k (Fin n), ρ u' (((ψ (superDiag (u : GL (Fin n) k)) : ℂ))⁻¹ • ρ u v0)
        = ∑ u : unipB k (Fin n), (fun w : unipB k (Fin n) =>
            ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) : GL (Fin n) k)) : ℂ))⁻¹ •
              ρ w v0) (⟨u', hu'⟩ * u) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      _ = ∑ w : unipB k (Fin n), ((ψ (superDiag (((⟨u', hu'⟩ : unipB k (Fin n))⁻¹ * w : unipB k (Fin n)) :
            GL (Fin n) k)) : ℂ))⁻¹ • ρ w v0 := Fintype.sum_equiv (Equiv.mulLeft a) (fun u => F (a * u)) F (fun _ => rfl)
      _ = _ := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hχ, mul_inv, inv_inv, mul_smul]

theorem vanish_of_comm {n : ℕ} {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin n), ρ u v = (ψ (superDiag u) : ℂ) • v) {Y u₁ u₂ : GL (Fin n) k}
    (h1 : u₁ ∈ unipB k (Fin n)) (h2 : u₂ ∈ unipB k (Fin n)) (hc : u₁ * Y = Y * u₂)
    (hne : ψ (superDiag u₁) ≠ ψ (superDiag u₂)) : l (ρ Y v) = 0 := by
  have e1 : l (ρ (u₁ * Y) v) = ψ (superDiag u₁) * l (ρ Y v) := by rw [map_mul, Module.End.mul_apply, hl u₁ h1]
  have e2 : l (ρ (Y * u₂) v) = ψ (superDiag u₂) * l (ρ Y v) := by
    rw [map_mul, Module.End.mul_apply, hv u₂ h2, map_smul, map_smul, smul_eq_mul]
  rw [hc, e2] at e1
  have hne' : (ψ (superDiag u₁) : ℂ) ≠ ψ (superDiag u₂) := fun h => hne (Circle.ext h)
  have : ((ψ (superDiag u₂) : ℂ) - ψ (superDiag u₁)) * l (ρ Y v) = 0 := by rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne'.symm)

theorem vanish_lower {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) {ρ : Representation ℂ (GL (Fin (m + 1)) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin (m + 1)), ρ u v = (ψ (superDiag u) : ℂ) • v) (Y : GL (Fin (m + 1)) k)
    (hlow : ∀ r c : Fin (m + 1), r < c → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = 0)
    (hlast : ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c) (hY : Y ≠ 1) : l (ρ Y v) = 0 := by
  classical
  set S := Finset.univ.filter fun r : Fin (m + 1) =>
    ∃ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c ≠ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c with hSdef
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hY
    ext r c
    have := h (Finset.mem_univ r)
    push_neg at this
    rw [this c, Units.val_one]
  have hr₀ := Finset.max'_mem S hS
  have hle : ∀ r ∈ S, r ≤ S.max' hS := fun r hr => Finset.le_max' S r hr
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀, S.max' hS = r₀ := ⟨_, rfl⟩
  rw [hr₀def] at hr₀ hle
  have hmax : ∀ r, r₀ < r → ∀ c, (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c := fun r hr c => by
    by_contra h
    exact absurd (hle r (by rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, c, h⟩)) (not_le.2 hr)
  rw [hSdef, Finset.mem_filter] at hr₀
  obtain ⟨j, hj⟩ := hr₀.2
  have hr₀last : r₀ ≠ Fin.last m := fun h => by rw [h] at hj; exact hj (hlast j)
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hr₀last
  have hjle : j ≤ r₀ := by
    by_contra h
    push_neg at h
    exact hj (by rw [hlow _ _ h, Matrix.one_apply_ne (ne_of_lt h)])
  have hcgt : r₀ < i.succ := by rw [← hi]; exact Fin.castSucc_lt_succ
  have hrow := hmax _ hcgt
  have hcol : ∀ r, r₀ < r → (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r j = 0 := fun r hr => by
    rw [hmax r hr j, Matrix.one_apply_ne (lt_of_le_of_lt hjle hr).ne']
  have hd : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j ≠ 0 :=
    sub_ne_zero.2 hj
  obtain ⟨s₀, hs₀⟩ := AddChar.ne_one_iff.1 hψ
  have h1' : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j = 0 := by rw [hcol _ hcgt, mul_zero]
  have h2' : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) i.succ = 0 := by
    rw [Pi.single_apply, if_neg (lt_of_le_of_lt hjle hcgt).ne']
  refine vanish_of_comm hl hv
    (colElt_mem _ _ h1' fun r hr => by rw [hcol r (lt_trans hcgt hr), mul_zero])
    (colElt_mem _ _ h2' fun r hr => by rw [Pi.single_apply, if_neg (lt_trans (lt_of_le_of_lt hjle hcgt) hr).ne'])
    (colElt_comm Y i.succ j _ hrow h1' h2') ?_
  rw [superDiag_colElt, superDiag_colElt, hi]
  have hsY : s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j + s₀ := by
    field_simp
    ring
  have hsing : (Pi.single j (s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j -
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j)) : Fin (m + 1) → k) r₀ =
      s₀ / ((Y : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j) *
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r₀ j := by
    by_cases h : r₀ = j
    · subst h; simp
    · rw [Pi.single_apply, if_neg h, Matrix.one_apply_ne h, mul_zero]
  rw [hsY, hsing, AddChar.map_add_eq_mul]
  intro h
  exact hs₀ (by simpa using h)

end DiscreteGroups.sglob.DzFp
end
end

section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands DiscreteGroups.sglob.DzRed

namespace DiscreteGroups.sglob.DzFp

variable {k : Type} [Field k] [Fintype k] [DecidableEq k] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_cell {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : GL (Fin m) k → ℂ)
    (h1 : ∀ u ∈ unipB k (Fin m), ∀ x, W (u * x) = (((ψ (superDiag u))⁻¹ : Circle) : ℂ) * W x)
    (h2 : ∀ b ∈ lowB k m, ∀ x, W (x * b) = W x) (L : GL (Fin m) k → ℂ)
    (hL : ∀ u ∈ unipB k (Fin m), ∀ x, L (u * x) = (ψ (superDiag u) : ℂ) * L x) :
    ∑ᶠ x, L x * W x = (Nat.card (unipB k (Fin m)) : ℂ) * W 1 * ∑ᶠ b : lowB k m, L b := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  have hinj : Function.Injective (fun p : unipB k (Fin m) × lowB k m => (p.1 : GL (Fin m) k) * p.2) := by
    rintro ⟨u, b⟩ ⟨u', b'⟩ h
    simp only at h
    have h3 : ((u' : GL (Fin m) k)⁻¹ * u : GL (Fin m) k) = b' * (b : GL (Fin m) k)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, inv_mul_cancel_left]
    have h4 : ((u' : GL (Fin m) k)⁻¹ * u : GL (Fin m) k) = 1 :=
      eq_one_of_unip_lower (mul_mem (inv_mem u'.2) u.2) (by rw [h3]; exact mem_lowB.1 (mul_mem b'.2 (inv_mem b.2)))
    have hu : u = u' := Subtype.ext (inv_mul_eq_one.1 h4).symm
    subst hu
    have hb : b = b' := Subtype.ext (mul_left_cancel h)
    rw [hb]
  calc ∑ x, L x * W x
      = ∑ x ∈ Finset.univ.image (fun p : unipB k (Fin m) × lowB k m => (p.1 : GL (Fin m) k) * p.2), L x * W x := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
        by_contra hne
        have hW : W x ≠ 0 := fun h => hne (by rw [h, mul_zero])
        obtain ⟨u, hu, b, hb, rfl⟩ := supp ψ hψ W h1 h2 x hW
        exact hx (Finset.mem_image.2 ⟨(⟨u, hu⟩, ⟨b, hb⟩), Finset.mem_univ _, rfl⟩)
    _ = ∑ p : unipB k (Fin m) × lowB k m, L (p.1 * p.2) * W (p.1 * p.2) :=
        Finset.sum_image (fun p _ q _ h => hinj h)
    _ = ∑ p : unipB k (Fin m) × lowB k m, L p.2 * W 1 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have hW1 : W p.2 = W 1 := by simpa using h2 _ p.2.2 1
        have hz := Circle.coe_ne_zero (ψ (superDiag (p.1 : GL (Fin m) k)))
        rw [hL _ p.1.2, h1 _ p.1.2, hW1, Circle.coe_inv]
        field_simp
    _ = _ := by
        simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
        ring

theorem corner_lower {m : ℕ} {b : GL (Fin m) k} (hb : b ∈ lowB k m) :
    ∀ r c : Fin (m + 1), r < c → (corner b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r c = 0 := by
  intro r c hrc
  induction r using Fin.lastCases with
  | last => exact absurd hrc (not_lt.2 (Fin.le_last _))
  | cast r =>
    induction c using Fin.lastCases with
    | last => exact corner_cs_last b r
    | cast c => rw [corner_cs_cs]; exact mem_lowB.1 hb r c (Fin.castSucc_lt_castSucc_iff.1 hrc)

theorem corner_last_row {m : ℕ} (b : GL (Fin m) k) (c : Fin (m + 1)) :
    (corner b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c := by
  induction c using Fin.lastCases with
  | last => rw [corner_last_last, Matrix.one_apply_eq]
  | cast c => rw [corner_last_cs, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne']

theorem corner_ne_one {m : ℕ} {b : GL (Fin m) k} (hb : b ≠ 1) : corner b ≠ 1 := by
  intro h
  apply hb
  ext i j
  have := congrArg (fun z : GL (Fin (m + 1)) k => (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc) h
  simp only [corner_cs_cs, Units.val_one, Matrix.one_apply, Fin.castSucc_inj] at this
  rw [this, Units.val_one, Matrix.one_apply]

theorem sum_lower_corner {m : ℕ} {ψ : AddChar k Circle} (hψ : ψ ≠ 1) {ρ : Representation ℂ (GL (Fin (m + 1)) k) V}
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) {v : V}
    (hv : ∀ u ∈ unipB k (Fin (m + 1)), ρ u v = (ψ (superDiag u) : ℂ) • v) :
    ∑ᶠ b : lowB k m, l (ρ (corner (b : GL (Fin m) k)) v) = l v := by
  classical
  rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single (1 : lowB k m)]
  · simp [corner_one]
  · intro b _ hb
    exact vanish_lower hψ hl hv _ (corner_lower b.2) (corner_last_row _)
      (corner_ne_one fun h => hb (Subtype.ext h))
  · simp

theorem corner_fixed {m : ℕ} (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (v : V) (b' : GL (Fin m) k)
    (hb' : b' ∈ lowB k m) :
    ρ (corner b') (∑ᶠ b : lowB k m, ρ (corner (b : GL (Fin m) k)) v) = ∑ᶠ b : lowB k m, ρ (corner (b : GL (Fin m) k)) v := by
  classical
  rw [finsum_eq_sum_of_fintype, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨b', hb'⟩ : lowB k m)) _ _ fun b => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, corner_mul, map_mul, Module.End.mul_apply]

theorem map_finsum_lower {m : ℕ} (f : V →ₗ[ℂ] ℂ) (F : lowB k m → V) : f (∑ᶠ b, F b) = ∑ᶠ b, f (F b) := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]

theorem map_finsum_lower' {m : ℕ} (f : V →ₗ[ℂ] V) (F : lowB k m → V) : f (∑ᶠ b, F b) = ∑ᶠ b, f (F b) := by
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]

end DiscreteGroups.sglob.DzFp
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.DzType

theorem lFinPair : LFinPair := by
  intro hLFE g _ m ψ₀ hψ τ hτ γ hγ l hl hl0 W hW s hs
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  classical
  have h1 : ∀ u ∈ unipB (ZMod g) (Fin m), ∀ x, W (u * x) = (((ψ₀ (superDiag u))⁻¹ : Circle) : ℂ) * W x := hW.1
  have h2 : ∀ b ∈ DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, ∀ x, W (x * b) = W x := fun b hb =>
    hW.2.1 b (DiscreteGroups.sglob.DzFp.mem_lowB.1 hb)
  obtain ⟨v, hv0, hv⟩ := DiscreteGroups.sglob.DzFp.exists_eigen hl hl0
  have hR := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun x => l (τ.ρ (corner x) v)) (fun u hu x => by
    show l (τ.ρ (corner (u * x)) v) = _ * l (τ.ρ (corner x) v)
    rw [DiscreteGroups.sglob.DzRed.corner_mul, map_mul, Module.End.mul_apply, hl _ (DiscreteGroups.sglob.DzRed.corner_mem hu),
      DiscreteGroups.sglob.DzRed.superDiag_corner])
  have hL := DiscreteGroups.sglob.DzFp.sum_cell hψ W h1 h2 (fun h => l (τ.ρ (tilde (corner (tilde h))) v)) (fun u hu x => by
    show l (τ.ρ (tilde (corner (tilde (u * x)))) v) = _ * l (τ.ρ (tilde (corner (tilde x))) v)
    rw [DiscreteGroups.sglob.DzRed.tilde_mul_left u x,
      DiscreteGroups.sglob.DzRed.corner_mul (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)
        (tilde x),
      DiscreteGroups.sglob.DzRed.tilde_mul_left
        (corner (longElt m (ZMod g) * GlobalTheory.CuspRep.invT m (ZMod g) u * (longElt m (ZMod g))⁻¹)) (corner (tilde x)),
      map_mul, Module.End.mul_apply,
      hl _ (DiscreteGroups.sglob.DzRed.conjT_mem (DiscreteGroups.sglob.DzRed.corner_mem (DiscreteGroups.sglob.DzRed.conjT_mem hu))),
      DiscreteGroups.sglob.DzRed.superDiag_conjT, ← DiscreteGroups.sglob.DzRed.corner_inv, DiscreteGroups.sglob.DzRed.superDiag_corner,
      ← DiscreteGroups.sglob.DzFp.conjT_inv, DiscreteGroups.sglob.DzRed.superDiag_conjT, inv_inv])
  have hre : ∑ᶠ x, l (τ.ρ (tilde (corner x)) v) * W (tilde x) =
      ∑ᶠ h, l (τ.ρ (tilde (corner (tilde h))) v) * W h := by
    have := finsum_comp_equiv (Function.Involutive.toPerm _ (DiscreteGroups.sglob.DzFp.tilde_tilde (R := ZMod g) (n := m)))
      (f := fun h => l (τ.ρ (tilde (corner (tilde h))) v) * W h)
    rw [← this]
    refine finsum_congr fun x => ?_
    show _ = l (τ.ρ (tilde (corner (tilde (tilde x)))) v) * W (tilde x)
    rw [DiscreteGroups.sglob.DzFp.tilde_tilde]
  have hs' := hs v
  rw [hre, hL, hR, DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv] at hs'
  set c := longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) with hcdef
  set X := ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, τ.ρ (corner (b : GL (Fin m) (ZMod g))) v with hXdef
  have hLsum : ∑ᶠ b : DiscreteGroups.sglob.DzFp.lowB (ZMod g) m, l (τ.ρ (tilde (corner (tilde (b : GL (Fin m) (ZMod g))))) v) =
      l (τ.ρ c X) := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower' (τ.ρ c), DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    refine finsum_congr fun b => ?_
    rw [DiscreteGroups.sglob.DzFp.tilde_corner, DiscreteGroups.sglob.DzFp.tilde_tilde, ← hcdef, map_mul, Module.End.mul_apply]
  rw [hLsum] at hs'
  have hfe := hLFE g m ψ₀ hψ τ hτ γ hγ l hl X fun b hb =>
    DiscreteGroups.sglob.DzFp.corner_fixed τ.ρ v b (DiscreteGroups.sglob.DzFp.mem_lowB.2 hb)
  have hlX : l X = l v := by
    rw [hXdef, DiscreteGroups.sglob.DzFp.map_finsum_lower l]
    exact DiscreteGroups.sglob.DzFp.sum_lower_corner hψ hl hv
  rw [hlX] at hfe
  have hK : (Nat.card (unipB (ZMod g) (Fin m)) : ℂ) * W 1 ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne') hW.2.2
  have hcX : l (τ.ρ c X) = s * l v := by
    apply mul_left_cancel₀ hK
    rw [hs']
    ring
  rw [hcX] at hfe
  apply mul_right_cancel₀ hv0
  rw [← hfe]
  ring

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

open NumberField IsDedekindDomain

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_eq_mulShift_toCircle (g : ℕ) [NeZero g] (l : AddChar (ZMod g) Circle) :
    ∃ s : ZMod g, l = (ZMod.toCircle : AddChar (ZMod g) Circle).mulShift s := by
  classical
  let e : AddChar (ZMod g) Circle → AddChar (ZMod g) ℂ := fun χ => Circle.coeHom.compAddChar χ
  have he : Function.Injective e :=
    MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)
  have hp : (e ZMod.toCircle).IsPrimitive := ZMod.isPrimitive_stdAddChar g
  have hbij : Function.Bijective (e ZMod.toCircle).mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩
  obtain ⟨s, hs⟩ := hbij.2 (e l)
  refine ⟨s, DFunLike.ext _ _ fun t => ?_⟩
  have := congrArg (fun χ : AddChar (ZMod g) ℂ => χ t) hs
  simp only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this
  rw [AddChar.mulShift_apply]
  exact (Circle.coe_inj.mp this).symm

theorem stdChar_shift_intCast (g : ℕ) [Fact g.Prime] (s : ZMod g) (x : ℤ_[g]) :
    GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * (x : ℚ_[g])) =
      ZMod.toCircle (s * PadicInt.toZMod x) := by
  have hg0 : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  set j : ZMod g := s * PadicInt.toZMod x with hj
  have hmem : (s.val : ℤ_[g]) * x - (j.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hj, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((s.val : ℚ_[g]) / g) * (x : ℚ_[g]) - ((j.val : ℤ) : ℚ_[g]) / (g : ℚ_[g]) ^ 1 = (c : ℚ_[g]) := by
    have := congrArg (fun z : ℤ_[g] => (z : ℚ_[g])) hc
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_sub] at this
    rw [pow_one]
    field_simp
    push_cast
    linear_combination (-1 : ℚ_[g]) * this
  rw [GroundTheory.LocalField.Padic.stdChar_apply g _ (j.val : ℤ) 1 (by rw [hc']; exact c.2),
    ZMod.toCircle_eq_circleExp, Real.fourierChar_apply']
  congr 1
  push_cast
  ring

theorem continuous_symm' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ}
    [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

theorem lPsi : LPsi := by
  intro E _ _ w g _ i hi ψ₀ h₀
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  obtain ⟨s, hs⟩ := exists_eq_mulShift_toCircle g ψ₀
  let ψQ : AddChar ℚ_[g] Circle := (GroundTheory.LocalField.Padic.stdChar g).mulShift ((s.val : ℚ_[g]) / g)
  let ψ : AddChar (w.adicCompletion E) Circle := ψQ.compAddMonoidHom i.symm.toAddMonoidHom
  have key : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x) := fun x => by
    show GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * i.symm (i (x : ℚ_[g]))) = ψ₀ _
    rw [RingEquiv.symm_apply_apply, stdChar_shift_intCast, hs, AddChar.mulShift_apply]
  refine ⟨ψ, ?_, ?_, key⟩
  · exact (GroundTheory.LocalField.Padic.continuous_stdChar g).comp (continuous_const.mul (continuous_symm' i hi))
  · intro h1
    apply h₀
    refine DFunLike.ext _ _ fun k => ?_
    obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := g)) k
    rw [← key, h1, AddChar.one_apply, AddChar.one_apply]

end DiscreteGroups.sglob.DzType
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sd_eq (A : Gn g (m + 1)) :
    superDiag A = ∑ l : Fin m, (A : Mt g (m + 1)) (Fin.castSucc l) (Fin.succ l) := by
  unfold superDiag
  simp_rw [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_eq_zero (fun k _ => if_neg (by have := k.2; simp only [Fin.val_last]; omega)), add_zero]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_eq_single (Fin.succ l)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by simp [h]))
  · simp

theorem trace_phi (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    trace ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) - ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) 0 0 =
      superDiag (umGL p.1) := by
  rw [phi_val]
  simp only [Matrix.trace, Matrix.diag, cyc_mul_apply]
  rw [← Equiv.sum_comp (finRotate (m + 1))]
  simp only [Equiv.symm_apply_apply]
  rw [Fin.sum_univ_castSucc, finRotate_last, rot_symm_zero, add_sub_cancel_right, sd_eq, umGL_val]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [rot_castSucc, hp_um_row _ _ _ (Fin.castSucc_lt_last l).ne]

theorem isRowFix_conj {j : ℕ} (r : Fin (m + 1) → ZMod g) (hr : ∀ l : Fin (m + 1), (l : ℕ) ≤ j → r l = 0)
    (hr0 : r (Fin.last m) ≠ 0) : IsRowFix j (cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹) := by
  have he : ∀ i k, ((cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) i k =
      Hp r ((finRotate (m + 1)).symm i) ((finRotate (m + 1)).symm k) := fun i k => by
    rw [Units.val_mul, Units.val_mul, mul_cycinv_apply, cyc_mul_apply, hpGL_val]
  refine ⟨fun i k hi => ?_, fun i k hi hk0 hk => ?_⟩
  · have hi' : i ≠ 0 := fun h => hi (by simp [h])
    rw [he]
    simp only [Hp, Matrix.of_apply, if_neg (rot_symm_ne_last i hi'), Matrix.one_apply,
      (finRotate (m + 1)).symm.apply_eq_iff_eq]
  · have hi' : i = 0 := Fin.ext hi
    have hk' : k ≠ 0 := fun h => by simp [h] at hk0
    subst hi'
    rw [he, rot_symm_zero]
    simp only [Hp, Matrix.of_apply, if_pos rfl]
    have hv := rot_symm_val k hk'
    exact hr _ (by omega)

theorem phi_inj {j : ℕ} {p q : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)} (h : phi j p = phi j q) :
    p = q := by
  obtain ⟨N1, t1, w1⟩ := p
  obtain ⟨N2, t2, w2⟩ := q
  unfold phi at h
  rw [mul_assoc, mul_assoc] at h
  have h1 := mul_left_cancel h
  have hz := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1))) h1
  simp only [Units.val_mul, hpGL_val, umGL_val] at hz
  have hN : N1 = N2 := by
    funext q
    have hne : q.1.1 ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le q.2 (Fin.le_last _))
    have := congrFun (congrFun hz q.1.1) q.1.2
    rw [hp_um_row _ _ _ hne, hp_um_row _ _ _ hne] at this
    simpa [Um, ne_of_lt q.2, q.2] using this
  subst hN
  have h2 := mul_right_cancel h1
  have hr : ∀ k, rvec j t1 w1 k = rvec j t2 w2 k := fun k => by
    have := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1)) (Fin.last m) k) h2
    simpa [hpGL_val, Hp] using this
  have ht : t1 = t2 := Units.ext (by simpa [rvec_last] using hr (Fin.last m))
  have hw : w1 = w2 := by
    funext q
    have hq : q.1 ≠ Fin.last m := fun e => by
      have := q.2.2
      rw [e, Fin.val_last] at this
      omega
    simpa [rvec, hq, q.2] using hr q.1
  rw [ht, hw]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem phi_surj {j : ℕ} (_hj : j < m) (y : Gn g (m + 1)) (hy : IsY j (y : Mt g (m + 1))) :
    ∃ p, phi j p = y := by
  set z : Gn g (m + 1) := (cyc g (m + 1))⁻¹ * y with hzdef
  have hz : ∀ l k, (z : Mt g (m + 1)) l k = (y : Mt g (m + 1)) (finRotate (m + 1) l) k := fun l k => by
    rw [hzdef, Units.val_mul, cycinv_mul_apply]
  set N : SIdx m → ZMod g := fun q => (z : Mt g (m + 1)) q.1.1 q.1.2 with hNdef
  have hzU : ∀ l, l ≠ Fin.last m → ∀ k, (z : Mt g (m + 1)) l k = Um N l k := by
    intro l hl k
    have hσ : ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = l + 1 := coe_finRotate_of_ne_last hl
    by_cases hkl : k ≤ l
    · have hkl' : (k : ℕ) ≤ l := hkl
      rw [hz, hy.2 k (finRotate (m + 1) l) (by rw [Fin.lt_def, hσ]; omega)]
      simp only [Um, Matrix.of_apply]
      by_cases e : k = l
      · subst e
        rw [if_pos hσ, if_pos rfl]
      · have e' : l ≠ k := Ne.symm e
        have hlk : ¬ l < k := not_lt.2 hkl
        have e2 : ¬ ((finRotate (m + 1) l : Fin (m + 1)) : ℕ) = (k : ℕ) + 1 := by
          rw [hσ]
          intro h'
          exact e (Fin.ext (by omega))
        rw [if_neg e2, if_neg e', dif_neg hlk]
    · have hlk : l < k := not_le.1 hkl
      simp only [Um, Matrix.of_apply, if_neg (ne_of_lt hlk), dif_pos hlk, hNdef]
  set U : Gn g (m + 1) := umGL N with hUdef
  set h : Gn g (m + 1) := z * U⁻¹ with hhdef
  have hrow : ∀ l, l ≠ Fin.last m → ∀ k, (h : Mt g (m + 1)) l k = (1 : Mt g (m + 1)) l k := by
    intro l hl k
    rw [hhdef, Units.val_mul, Matrix.mul_apply]
    simp_rw [hzU l hl]
    rw [← Matrix.mul_apply, ← umGL_val, ← hUdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hUinv : (((U⁻¹ : Gn g (m + 1)) : Mt g (m + 1))).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    let _ := U.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular (um_upper N)
  have hlast : ∀ k : Fin (m + 1), (k : ℕ) ≤ j → (h : Mt g (m + 1)) (Fin.last m) k = 0 := by
    intro k hk
    rw [hhdef, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    by_cases ha : (a : ℕ) ≤ j
    · rw [hz, finRotate_last, hy.1 a ha, zero_mul]
    · rw [hUinv (show k < a by rw [Fin.lt_def]; omega), mul_zero]
  have hdet : (h : Mt g (m + 1)) (Fin.last m) (Fin.last m) ≠ 0 := by
    have hl : (h : Mt g (m + 1)).BlockTriangular OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      have ha : a ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hab' (Fin.le_last b))
      rw [hrow a ha, Matrix.one_apply_ne (ne_of_lt hab')]
    have hd : (h : Mt g (m + 1)).det = (h : Mt g (m + 1)) (Fin.last m) (Fin.last m) := by
      rw [Matrix.det_of_lowerTriangular _ hl, Fin.prod_univ_castSucc]
      simp [hrow _ (Fin.castSucc_lt_last _).ne]
    rw [← hd]
    exact IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit)
  set t : (ZMod g)ˣ := Units.mk0 _ hdet with htdef
  set w : WIdx m j → ZMod g := fun q => (h : Mt g (m + 1)) (Fin.last m) q.1 with hwdef
  refine ⟨(N, t, w), ?_⟩
  have hH : hpGL (rvec j t w) (by rw [rvec_last]; exact t.ne_zero) = h := by
    apply Units.ext
    ext a b
    rw [hpGL_val]
    simp only [Hp, Matrix.of_apply]
    by_cases ha : a = Fin.last m
    · subst ha
      rw [if_pos rfl]
      simp only [rvec]
      by_cases hb : b = Fin.last m
      · subst hb
        simp [htdef]
      · rw [if_neg hb]
        split_ifs with hb2
        · rfl
        · have hbm : (b : ℕ) ≠ m := fun e => hb (Fin.ext (by simp [e]))
          have := b.2
          have hbj : (b : ℕ) ≤ j := by
            by_contra hc
            exact hb2 ⟨by omega, by omega⟩
          exact (hlast b hbj).symm
    · rw [if_neg ha, hrow a ha]
  show cyc g (m + 1) * hpGL (rvec j t w) _ * umGL N = y
  rw [hH, hhdef, hzdef, ← hUdef]
  group

theorem card_P (j : ℕ) :
    Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) =
      g ^ Fintype.card (SIdx m) * (g - 1) * g ^ Fintype.card (WIdx m j) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card_units]
  ring

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem rho_mul_inv_self (a : Gn g (m + 1)) (x : τ) : τ.ρ a (τ.ρ a⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_mul_self (a : Gn g (m + 1)) (x : τ) : τ.ρ a⁻¹ (τ.ρ a x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rhs_sum {j : ℕ} (hj : j < m) (l : Module.Dual ℂ τ) (hl : IsFunctional ψ₀ τ.ρ l) (v : τ)
    (hB : ∀ h, IsRowFix j h → τ.ρ h v = v) :
    ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
        (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v) else 0) =
      (Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : ℂ) *
        l (τ.ρ (cyc g (m + 1))⁻¹ v) := by
  rw [← Finset.sum_filter]
  have key := Finset.sum_bij (s := (Finset.univ : Finset ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g))))
    (t := Finset.univ.filter (fun y : Gn g (m + 1) => IsY j (y : Mt g (m + 1))))
    (f := fun _ => l (τ.ρ (cyc g (m + 1))⁻¹ v))
    (g := fun y => (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v))
    (fun p _ => phi j p)
    (fun p _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, isY_phi hj p⟩)
    (fun p _ q _ h => phi_inj h)
    (fun y hy => by
      obtain ⟨p, hp⟩ := phi_surj hj y (Finset.mem_filter.1 hy).2
      exact ⟨p, Finset.mem_univ _, hp⟩)
    (fun p _ => by
      obtain ⟨N, t, w⟩ := p
      show _ = (ψ₀ (trace ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) -
        ((phi j (N, t, w) : Gn g (m + 1)) : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ (phi j (N, t, w))⁻¹ v)
      rw [trace_phi]
      have hr0 : rvec j t w (Fin.last m) ≠ 0 := by rw [rvec_last]; exact t.ne_zero
      set H := hpGL (rvec j t w) hr0
      have hinv : (phi j (N, t, w))⁻¹ =
          (umGL N)⁻¹ * (cyc g (m + 1))⁻¹ * (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹ := by
        simp only [phi]
        group
        rfl
      have hX : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹) v = v :=
        hB _ (isRowFix_conj _ (fun l hl => rvec_low hj t w l hl) hr0)
      have hX' : τ.ρ (cyc g (m + 1) * H * (cyc g (m + 1))⁻¹)⁻¹ v = v := by
        conv_lhs => rw [← hX]
        exact rho_inv_mul_self τ _ v
      rw [hinv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hX']
      have := hl (umGL N) (umGL_mem N) (τ.ρ (umGL N)⁻¹ (τ.ρ (cyc g (m + 1))⁻¹ v))
      rw [rho_mul_inv_self] at this
      exact this)
  rw [← key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sum_range_lt (n k : ℕ) : ∑ x ∈ Finset.range n, (if x < k then 1 else 0) = min n k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.lt_or_ge n k with h | h
    · rw [if_pos h, min_eq_left h.le, min_eq_left (by omega)]
    · rw [if_neg (by omega), min_eq_right h, min_eq_right (by omega), add_zero]

theorem card_SIdx : Fintype.card (SIdx m) = (m + 1) * m / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ k : Fin (m + 1), ∑ i : Fin (m + 1), (if (i, k).1 < (i, k).2 then 1 else 0) = (k : ℕ) := fun k => by
    show ∑ i : Fin (m + 1), (if (i : ℕ) < (k : ℕ) then 1 else 0) = (k : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun x => if x < (k : ℕ) then 1 else 0), sum_range_lt]
    exact min_eq_right k.2.le
  rw [Finset.sum_congr rfl (fun k _ => h k), Fin.sum_univ_eq_sum_range (fun x => x), Finset.sum_range_id]
  simp

theorem sum_range_between (n j m : ℕ) :
    ∑ x ∈ Finset.range n, (if j < x ∧ x < m then 1 else 0) = min n m - min n (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.min_def]
    split_ifs <;> omega

theorem card_WIdx (j : ℕ) : Fintype.card (WIdx m j) = m - 1 - j := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun x => if j < x ∧ x < m then 1 else 0), sum_range_between]
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem sum_split (j : ℕ) (f : ZMod g → ℂ) :
    ∑ b : JIdx m j → ZMod g, f (b (j0 m j)) =
      (Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) : ℂ) * ∑ s : ZMod g, f s := by
  rw [← (Equiv.funSplitAt (j0 m j) (ZMod g)).symm.sum_comp, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp [Equiv.funSplitAt_symm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

theorem fe : FunctionalEquationAtIndex := by
  intro g _ m ψ₀ hψ τ hτ γ hγ l hl j hj v hA hB
  have hm : 0 < m := by omega
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hg1 : (g : ℂ) - 1 ≠ 0 := by
    have : g ≠ 1 := (Fact.out : g.Prime).ne_one
    exact sub_ne_zero.2 (by exact_mod_cast this)
  set K : ℕ := Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) with hK
  have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcardJ : (g : ℂ) ^ Fintype.card (JIdx m j) = (K : ℂ) * g := by
    have := sum_split (g := g) (m := m) j (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun, ZMod.card,
      Nat.cast_pow] at this
    rw [hK, Fintype.card_fun, ZMod.card, Nat.cast_pow]
    exact this
  set X : ℂ := l (τ.ρ (cyc g (m + 1))⁻¹ v) with hX
  have hL : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (SIdx m) * ((K : ℂ) * (((g : ℂ) - 1) * (γ * l v))) := by
    rw [Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => lhs_term ψ₀ τ hγ hτ hm l hl v hA N b))]
    have hb : ∑ b : JIdx m j → ZMod g, (if b (j0 m j) = 0 then (0 : ℂ) else γ * l v) =
        (K : ℂ) * (((g : ℂ) - 1) * (γ * l v)) := by
      have hs := sum_split (g := g) (m := m) j (fun s => if s = 0 then (0 : ℂ) else γ * l v)
      rw [hs]
      congr 1
      have h2 : ∑ s : ZMod g, (if s = 0 then (0 : ℂ) else γ * l v) =
          ∑ _s : ZMod g, γ * l v - ∑ s : ZMod g, (if s = 0 then γ * l v else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by split_ifs <;> ring)
      rw [h2, Finset.sum_const, Finset.card_univ, ZMod.card, Finset.sum_ite_eq' Finset.univ (0 : ZMod g),
        if_pos (Finset.mem_univ _), nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun N _ => hb), Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      nsmul_eq_mul]
    push_cast
    ring
  have e1 : ∀ (N : SIdx m → ZMod g) (b : JIdx m j → ZMod g),
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      ∑ y : Gn g (m + 1), (ψ₀ (-superDiag (umGL N)) : ℂ) *
        (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) * l (τ.ρ y⁻¹ v) := by
    intro N b
    simp only [sv, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hR : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
        ((Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : ℂ) * X) := by
    calc _ = ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g, ∑ y : Gn g (m + 1),
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => e1 N b))
      _ = ∑ N : SIdx m → ZMod g, ∑ y : Gn g (m + 1), ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_comm)
      _ = ∑ y : Gn g (m + 1), ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_comm
      _ = ∑ y : Gn g (m + 1), (∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ)) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun y _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun N _ => by rw [Finset.sum_mul]))
      _ = ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
          (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) else 0) * l (τ.ρ y⁻¹ v) :=
          Finset.sum_congr rfl (fun y _ => by rw [kern ψ₀ hψ j])
      _ = (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
          ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by split_ifs <;> ring)
      _ = _ := by rw [rhs_sum ψ₀ τ hj l hl v hB]
  have e := hL.symm.trans hR
  have hg1le : 1 ≤ g := (Fact.out : g.Prime).one_le
  rw [hcardJ, card_P, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hg1le,
    Nat.cast_one] at e
  have hne : (g : ℂ) ^ Fintype.card (SIdx m) * (K : ℂ) * ((g : ℂ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg) hK0) hg1
  have key : γ * l v = (g : ℂ) * (g : ℂ) ^ Fintype.card (SIdx m) * (g : ℂ) ^ Fintype.card (WIdx m j) * X :=
    mul_left_cancel₀ hne (by linear_combination e)
  have hexp : (m + 1) * m / 2 + m - j = Fintype.card (SIdx m) + Fintype.card (WIdx m j) + 1 := by
    rw [card_SIdx, card_WIdx]
    generalize (m + 1) * m / 2 = A
    omega
  rw [hexp, pow_add, pow_add, pow_one, key]
  ring

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := Equiv.apply_symm_apply σ x

theorem perm_inv_apply {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := Equiv.symm_apply_apply σ x

theorem cyc_mul_apply_rot {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n : Matrix (Fin n) (Fin n) (ZMod g)) * M) i l = M ((finRotate n)⁻¹ i) l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ i)]
  · show (if i = finRotate n ((finRotate n)⁻¹ i) then (1 : ZMod g) else 0) * _ = _
    rw [perm_apply_inv, if_pos rfl, one_mul]
  · intro a _ ha
    show (if i = finRotate n a then (1 : ZMod g) else 0) * _ = 0
    rw [if_neg, zero_mul]
    intro h; apply ha; rw [h, perm_inv_apply]
  · simp

theorem mul_cycInv_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    (M * (((cyc g n)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g))) i l =
      M i ((finRotate n)⁻¹ l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((finRotate n)⁻¹ l)]
  · show _ * (if finRotate n ((finRotate n)⁻¹ l) = l then (1 : ZMod g) else 0) = _
    rw [perm_apply_inv, if_pos rfl, mul_one]
  · intro a _ ha
    show _ * (if finRotate n a = l then (1 : ZMod g) else 0) = 0
    rw [if_neg, mul_zero]
    intro h; apply ha; rw [← h, perm_inv_apply]
  · simp

theorem mul_cyc_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod g)) (i l : Fin n) :
    (M * (cyc g n : Matrix (Fin n) (Fin n) (ZMod g))) i l = M i (finRotate n l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (finRotate n l)]
  · show _ * (if finRotate n l = finRotate n l then (1 : ZMod g) else 0) = _
    rw [if_pos rfl, mul_one]
  · intro a _ ha
    show _ * (if a = finRotate n l then (1 : ZMod g) else 0) = 0
    rw [if_neg ha, mul_zero]
  · simp

theorem cyc_conj_apply {n : ℕ} (M : GL (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n * M * (cyc g n)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      (M : Matrix (Fin n) (Fin n) (ZMod g)) ((finRotate n)⁻¹ i) ((finRotate n)⁻¹ l) := by
  rw [Units.val_mul, Units.val_mul, mul_cycInv_apply, cyc_mul_apply_rot]

theorem conj_apply {n : ℕ} (k : ℕ) (M : GL (Fin n) (ZMod g)) (i l : Fin n) :
    ((cyc g n ^ k * M * (cyc g n ^ k)⁻¹ : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      (M : Matrix (Fin n) (Fin n) (ZMod g)) ((finRotate n ^ k)⁻¹ i) ((finRotate n ^ k)⁻¹ l) := by
  induction k generalizing M with
  | zero => simp
  | succ k ih =>
    have e : cyc g n ^ (k + 1) * M * (cyc g n ^ (k + 1))⁻¹ =
        cyc g n ^ k * (cyc g n * M * (cyc g n)⁻¹) * (cyc g n ^ k)⁻¹ := by
      simp only [pow_succ, _root_.mul_inv_rev, mul_assoc]
    rw [e, ih, cyc_conj_apply, pow_succ, _root_.mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem cyc_pow_apply {n : ℕ} (k : ℕ) (i l : Fin n) :
    ((cyc g n ^ k : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) i l =
      if i = (finRotate n ^ k) l then 1 else 0 := by
  induction k generalizing l with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, mul_cyc_apply, ih, pow_succ, Equiv.Perm.mul_apply]

theorem rot_val {m : ℕ} (a : Fin (m + 1)) : ∀ k ≤ m,
    ((finRotate (m + 1) ^ k) a : ℕ) = (a : ℕ) + k ∨ ((finRotate (m + 1) ^ k) a : ℕ) + (m + 1) = (a : ℕ) + k := by
  intro k hk
  induction k with
  | zero => left; simp
  | succ k ih =>
    have ih := ih (by omega)
    have ha := a.isLt
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last] at ih; right; omega
    · have := Fin.val_lt_last h
      omega

theorem rot_inv_val {m k : ℕ} (hk : k ≤ m) (i : Fin (m + 1)) :
    (i : ℕ) = (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) + k ∨
      (i : ℕ) + (m + 1) = (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) + k := by
  have := rot_val ((finRotate (m + 1) ^ k)⁻¹ i) k hk
  rwa [perm_apply_inv] at this

theorem cyc_pow_eq_one (m : ℕ) : cyc g (m + 1) ^ (m + 1) = 1 := by
  have hr : ∀ l : Fin (m + 1), (finRotate (m + 1) ^ (m + 1)) l = l := by
    intro l
    have hv := rot_val l m le_rfl
    have hl := l.isLt
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_succ_apply]
    ext
    rw [Fin.val_add_one]
    split_ifs with h
    · rw [h, Fin.val_last] at hv; omega
    · have := Fin.val_lt_last h
      omega
  apply Units.ext
  ext i l
  rw [cyc_pow_apply, hr, Units.val_one, Matrix.one_apply]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem longElt_corner_eq_cyc (m : ℕ) :
    longElt (m + 1) (ZMod g) * corner (longElt m (ZMod g)) = cyc g (m + 1) := by
  apply Units.ext
  ext i k
  rw [Units.val_mul, DzRed.longElt_mul_apply]
  show _ = if i = finRotate (m + 1) k then (1 : ZMod g) else 0
  have hrv : ((Fin.rev i : Fin (m + 1)) : ℕ) = m - i := by rw [Fin.val_rev]; omega
  have hil := i.isLt
  rcases Fin.eq_castSucc_or_eq_last (Fin.rev i) with ⟨d, hd⟩ | hd
  · rw [hd]
    have hdv : (d : ℕ) = m - i := by rw [← hrv, hd, Fin.coe_castSucc]
    have hdl := d.isLt
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_cs_cs, DzRed.val_longElt]
      have hc : ((finRotate (m + 1) c.castSucc : Fin (m + 1)) : ℕ) = c + 1 := by
        rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc]
      have hcl := c.isLt
      by_cases h : c = d.rev
      · rw [if_pos h, if_pos]
        ext
        rw [hc]
        have := congrArg Fin.val h
        rw [Fin.val_rev] at this
        omega
      · rw [if_neg h, if_neg]
        intro e
        apply h
        ext
        have := congrArg Fin.val e
        rw [hc] at this
        rw [Fin.val_rev]
        omega
    · rw [DzRed.corner_cs_last, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero] at this
      omega
  · rw [hd]
    have hi0 : (i : ℕ) = 0 := by
      have := congrArg Fin.val hd
      rw [hrv, Fin.val_last] at this
      omega
    rcases Fin.eq_castSucc_or_eq_last k with ⟨c, rfl⟩ | rfl
    · rw [DzRed.corner_last_cs, if_neg]
      intro e
      have := congrArg Fin.val e
      rw [finRotate_succ_apply, Fin.val_add_one, if_neg (Fin.castSucc_lt_last c).ne, Fin.coe_castSucc] at this
      omega
    · rw [DzRed.corner_last_last, if_pos]
      ext
      rw [finRotate_succ_apply, Fin.last_add_one, Fin.val_zero, hi0]

theorem exists_corner [Fact g.Prime] {m : ℕ} (M : GL (Fin (m + 1)) (ZMod g))
    (hr : ∀ l, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) (Fin.last m) l = if l = Fin.last m then 1 else 0)
    (hc : ∀ i, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i (Fin.last m) = if i = Fin.last m then 1 else 0)
    (hlow : ∀ i l : Fin m, i < l → (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)) i.castSucc l.castSucc = 0) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = M := by
  have hne : ∀ j : Fin m, j.castSucc ≠ Fin.last m := fun j => (Fin.castSucc_lt_last j).ne
  set A : Matrix (Fin m) (Fin m) (ZMod g) :=
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).submatrix Fin.castSucc Fin.castSucc with hA
  have he : ((-1 : ZMod g) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod g)).det = A.det := by
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hr, hne, Fin.succAbove_last, A, he]
  have hAd : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAd, fun i l hil => hlow i l hil, ?_⟩
  apply Units.ext
  ext i l
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
  · rw [DzRed.corner_cs_cs]; rfl
  · rw [DzRed.corner_cs_last, hc, if_neg (hne i)]
  · rw [DzRed.corner_last_cs, hr, if_neg (hne l)]
  · rw [DzRed.corner_last_last, hr, if_pos rfl]

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

open Matrix GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ}

theorem colFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsColFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hb := rot_inv_val hk.le l
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hll := l.isLt
    rw [Fin.val_last] at ha
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) hb0 (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ hb0]
      by_cases e : l = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at hb
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) (by omega)]
    by_cases e : i = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hal := ((finRotate (m + 1) ^ k)⁻¹ i.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases hb0 : (((finRotate (m + 1) ^ k)⁻¹ l.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) hb0 (by omega)
    · rw [hh.1 _ _ hb0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

theorem rowFix_conj [Fact g.Prime] {m k : ℕ} (hk : k < m) (h : GL (Fin (m + 1)) (ZMod g))
    (hh : IsRowFix (m - 1 - k) h) :
    ∃ b : GL (Fin m) (ZMod g), (∀ i l : Fin m, i < l → (b : Matrix (Fin m) (Fin m) (ZMod g)) i l = 0) ∧
      corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹ := by
  apply exists_corner
  · intro l
    rw [conj_apply]
    have ha := rot_inv_val hk.le (Fin.last m)
    have hal := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    rw [Fin.val_last] at ha
    rw [hh.1 ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ((finRotate (m + 1) ^ k)⁻¹ l) (by omega)]
    by_cases e : l = Fin.last m
    · subst e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2; exact e (Equiv.injective _ e2).symm
  · intro i
    rw [conj_apply]
    have ha := rot_inv_val hk.le i
    have hb := rot_inv_val hk.le (Fin.last m)
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)).isLt
    have hil := i.isLt
    rw [Fin.val_last] at hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i : Fin (m + 1)) : ℕ) = 0
    · rw [hh.2 ((finRotate (m + 1) ^ k)⁻¹ i) ((finRotate (m + 1) ^ k)⁻¹ (Fin.last m)) ha0 (by omega)
        (by omega), if_neg]
      intro e
      have := congrArg Fin.val e
      rw [Fin.val_last] at this
      omega
    · rw [hh.1 _ _ ha0]
      by_cases e : i = Fin.last m
      · subst e; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg e, if_neg]
        intro e2; exact e (Equiv.injective _ e2)
  · intro i l hil
    rw [conj_apply]
    have ha := rot_inv_val hk.le i.castSucc
    have hb := rot_inv_val hk.le l.castSucc
    have hbl := ((finRotate (m + 1) ^ k)⁻¹ l.castSucc).isLt
    have hil' : (i : ℕ) < l := hil
    have hll := l.isLt
    rw [Fin.coe_castSucc] at ha hb
    by_cases ha0 : (((finRotate (m + 1) ^ k)⁻¹ i.castSucc : Fin (m + 1)) : ℕ) = 0
    · exact hh.2 ((finRotate (m + 1) ^ k)⁻¹ i.castSucc) ((finRotate (m + 1) ^ k)⁻¹ l.castSucc) ha0
        (by omega) (by omega)
    · rw [hh.1 _ _ ha0, if_neg]
      intro e2
      have := congrArg Fin.val (Equiv.injective _ e2)
      rw [Fin.coe_castSucc, Fin.coe_castSucc] at this
      omega

end DiscreteGroups.sglob.DzFe
end
end

section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL GlobalTheory.LocLanglands Matrix

namespace DiscreteGroups.sglob.DzFe

theorem lFE_of_fe : FunctionalEquationAtIndex → DzType.LFE := by
  intro hfe g _ m ψ₀ hψ τ hτ γ hγ l hl x hx
  have hfix : ∀ k, ∀ h : Gn g (m + 1),
      (∃ b : GL (Fin m) (ZMod g), (∀ i j : Fin m, i < j → (b : Matrix (Fin m) (Fin m) (ZMod g)) i j = 0) ∧
        corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) →
      τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by
    rintro k h ⟨b, hb, hcb⟩
    have e : h * (cyc g (m + 1) ^ k)⁻¹ =
        (cyc g (m + 1) ^ k)⁻¹ * (cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) := by group
    calc τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (h * (cyc g (m + 1) ^ k)⁻¹) x := by rw [map_mul]; rfl
      _ = τ.ρ ((cyc g (m + 1) ^ k)⁻¹ * corner b) x := by rw [e, ← hcb]
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ (τ.ρ (corner b) x) := by rw [map_mul]; rfl
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by rw [hx b hb]
  have step : ∀ t, t < m → γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) =
      (g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x) := by
    intro t ht
    have hv : τ.ρ (cyc g (m + 1))⁻¹ (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x := by
      rw [pow_succ, _root_.mul_inv_rev, map_mul]; rfl
    have := hfe g m ψ₀ hψ τ hτ γ hγ l hl (m - 1 - t) (by omega) (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)
      (fun h hh => hfix t h (colFix_conj ht h hh)) (fun h hh => hfix t h (rowFix_conj ht h hh))
    rw [this, hv, show (m + 1) * m / 2 + m - (m - 1 - t) = (m + 1) * m / 2 + (t + 1) by omega]
  have key : ∀ t, t ≤ m → γ ^ t * l x =
      (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ih := ih (by omega)
      have h2 : (t + 1) * (t + 1 + 1) / 2 = t * (t + 1) / 2 + (t + 1) := by
        rw [show (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) by ring,
          Nat.add_mul_div_left _ _ (by norm_num)]
      have hE : t * ((m + 1) * m / 2) + t * (t + 1) / 2 + ((m + 1) * m / 2 + (t + 1)) =
          (t + 1) * ((m + 1) * m / 2) + (t + 1) * (t + 1 + 1) / 2 := by
        rw [h2]; ring
      calc γ ^ (t + 1) * l x = γ * (γ ^ t * l x) := by ring
        _ = γ * ((g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            rw [ih]
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * (γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            ring
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) *
            ((g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x)) := by
            rw [step t (by omega)]
        _ = _ := by rw [← mul_assoc, ← pow_add, hE]
  have hcm : (cyc g (m + 1) ^ m)⁻¹ = cyc g (m + 1) := by
    have h1 := cyc_pow_eq_one (g := g) m
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_right h1
  have hfin := key m le_rfl
  rw [hcm] at hfin
  have hexp : m * (m + 1) ^ 2 / 2 = m * ((m + 1) * m / 2) + m * (m + 1) / 2 := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
    have h1 : (m + 1) * m / 2 = r := by rw [mul_comm, hr]; omega
    have h2 : m * (m + 1) / 2 = r := by rw [hr]; omega
    have h3 : m * (m + 1) ^ 2 / 2 = r * (m + 1) := by
      rw [show m * (m + 1) ^ 2 = 2 * (r * (m + 1)) by
        rw [show m * (m + 1) ^ 2 = m * (m + 1) * (m + 1) by ring, hr]; ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [h1, h2, h3]; ring
  rw [longElt_corner_eq_cyc, hfin, hexp]

end DiscreteGroups.sglob.DzFe
end
end

section
namespace DiscreteGroups.sglob.DzType

theorem lFE : LFE := DiscreteGroups.sglob.DzFe.lFE_of_fe DiscreteGroups.sglob.DzFe.fe



end DiscreteGroups.sglob.DzType
end
