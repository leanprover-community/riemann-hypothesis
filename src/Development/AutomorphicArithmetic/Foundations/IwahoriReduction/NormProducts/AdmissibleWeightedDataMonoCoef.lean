import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.PushLoc
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.TraceHeckeCongruenceVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.STop0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OneLeLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ZetaClassCohomologyCompat
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTameRelationProjected
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubMulAddLeOfUltrametricReplace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEqOneOfIsUnitToZModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefSpanFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSystemExponentRaiseOfPrimePowSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocWsumProps

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Topology

private theorem UpperTheory.Kd.K4.isCompact_integralCoefficients {l : ℕ} [Fact l.Prime] (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  haveI : ContinuousSMul ℤ_[l] (PadicAlgCl l) := by
    refine ⟨?_⟩
    have : (fun q : ℤ_[l] × PadicAlgCl l => q.1 • q.2) = fun q => (q.1 : ℚ_[l]) • q.2 := by
      funext q; rfl
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  exact Submodule.isCompact_of_fg hfg

private theorem UpperTheory.Kd.K4.norm_le_one_of_mem_coefficient_ring {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨M, hM⟩ := (UpperTheory.Kd.K4.isCompact_integralCoefficients c).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
  have := hM _ (c.O.pow_mem ha n)
  rw [norm_pow] at this
  linarith

private theorem UpperTheory.Kd.K4.norm_nat_cast_prime_lt_one_padic_closure (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem UpperTheory.Kd.K4.topCocycle_finsetSum (hA : SApi) (hI : SInvApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n M : ℕ) {ι : Type} (S : Finset ι)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (h : ∀ i ∈ S, TopCoc X l N w n M (z i)) :
    TopCoc X l N w n M (fun σ => ∑ i ∈ S, z i σ) := by
  classical
  have hsum := (hA Ω ε X l n).2.2.2.1
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact (hI Ω ε X l N w n).2.2.2.2.1 ι S _ fun i hi => (h i hi).inv σ hσ
  · have e : (∑ i ∈ S, z i σ) + X.galB l σ (∑ i ∈ S, z i τ) = ∑ i ∈ S, (z i σ + X.galB l σ (z i τ)) := by
      rw [map_sum, Finset.sum_add_distrib]
    rw [e]
    exact hsum ι S _ _ fun i hi => (h i hi).coc σ hσ τ hτ
  · choose! T hT using fun i hi => (h i hi).loc
    refine ⟨S.biUnion T, fun σ hσ τ hτ hst => ?_⟩
    exact hsum ι S _ _ fun i hi => hT i hi σ hσ τ hτ fun a ha => hst a (Finset.mem_biUnion.2 ⟨i, hi, ha⟩)

private theorem UpperTheory.Kd.K4.cocycleBound_finsetSum (hC : SCohApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N) {A : Type} [CommGroup A]
    (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι) (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l)
    (h : ∀ i ∈ S, CohB X l N w n κ (z i) (z' i)) : CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  classical
  have hc := hC Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using hc.1.refl 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hc.2.2.1 _ _ _ _ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))).1

private theorem UpperTheory.Kd.K4.shiftedBound_finsetSum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (M : ℕ) {ι : Type} (S : Finset ι) (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) :
    shB X l M (fun σ => ∑ i ∈ S, z i σ) = ∑ i ∈ S, shB X l M (z i) := by
  funext s y
  simp [shB, Finset.sum_apply, map_sum]

private theorem UpperTheory.Kd.K4.pushforward_finsetSum {Γ : Type} [Group Γ] {B A M ι : Type} [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (π : B → A) (S : Finset ι) (f : ι → Γ → B → M) :
    GlobalTheory.KA.push π (∑ i ∈ S, f i) = ∑ i ∈ S, GlobalTheory.KA.push π (f i) := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.sum_apply]
  exact Finset.sum_comm

private def UpperTheory.Kd.K4.unitsPowPrimeReduction (l r : ℕ) : (ZMod (l ^ (r + 1)))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom

private theorem UpperTheory.Kd.K4.unitsReduction_coe (l r : ℕ) : (⇑(unitsPowPrimeReduction l r)) = redL l r := rfl

private theorem UpperTheory.Kd.K4.unitsReduction_surjective (l r : ℕ) [Fact l.Prime] : Function.Surjective (unitsPowPrimeReduction l r) :=
  ZMod.unitsMap_surjective (pow_dvd_pow l (Nat.le_succ r))

private def UpperTheory.Kd.K4.unitsLevelToPrimePowReduction (l n r N : ℕ) : (ZMod (topM l n r N))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom

attribute [-instance] GlobalTheory.KZ.ClsMod.neZero_pow

theorem UpperTheory.Kd.K4.mlOf2 :
    SymEx → SApi → SInvApi → SBStab → SSlD → SCohApi → SCycZ → STop0 → KatoClassNormCompatibleCyclotomic → KatoClassCompatibleModPowers → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N] (e : ℕ),
      Nat.Coprime l N → l ≠ 2 → 1 ≤ e → ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ → ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
      (pr : X.Fn l → Fin 2 → Qbar l) (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y ∧ (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro hSym hA hI hBS hS hC hZc hT hNr hNn l _ Ω _ _ _ ε X N _ e hlN hl2 he
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨c₁, hc₁⟩ := UpperTheory.Kd.K4.mlB hA hI hBS hS ε X l N (2 * e - 1) hN
  refine ⟨c₁, fun c₀ hc₀ ι gN A W pr x c d gm ψ cf hAd => ?_⟩
  obtain ⟨hc1, hd1, hcc, hdc, hadd, hsm, hint, heq, -, -, hg0, -⟩ := hAd
  have hk : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hcy := (hS Ω ε X N hN).2.2.2.2.2.2.2
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hg0 r₀⟩
  have hLaws : ∃ ws, UpperTheory.V.Z.Kato.Sym.Laws X l c d ws :=
    hSym Ω ε X l c d Fact.out hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hL : LiftsWith X l N (2 * e - 1) (cL X l N (2 * e - 1)) :=
    Classical.epsilon_spec (UpperTheory.Kd.K4.liftH ε X l N (2 * e - 1) hl2 hN hlN ⟨e - 1, by omega⟩)
  let κ : ∀ r, (Ω ≃ₐ[ℚ] Ω) →* (ZMod (l ^ r))ˣ := fun r => (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹
  have hκ : ∀ r s, κ r s = (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := fun _ _ => rfl
  let zz : ℕ → ℕ → (Ω ≃ₐ[ℚ] Ω) → X.Fn l := fun n r σ => ∑ r₀, cls0 X l n r N x c d (2 * e - 1) (gm r₀) σ
  let Z : ∀ (_ r : ℕ), (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → X.Fn l := fun n r s y =>
    GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) (zz n r)) s (y * 1)
  have hZeq : ∀ n r, Z n r = ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) := by
    intro n r
    funext s y
    have e1 : shB X l (topM l n r (N * N)) (zz n r) =
        ∑ r₀, shB X l (topM l n r (N * N)) (cls0 X l n r N x c d (2 * e - 1) (gm r₀)) :=
      shiftedBound_finsetSum X l _ _ _
    simp only [Z, e1, pushforward_finsetSum, Finset.sum_apply, mul_one]
    rfl
  have hπκ : ∀ r s, unitsPowPrimeReduction l r (κ (r + 1) s) = κ r s := by
    intro r s
    rw [hκ, hκ, map_inv, (hZc Ω l (r + 1) s).1, (hZc Ω l r s).1]
    exact congrArg (·⁻¹) ((hcy (l ^ (r + 1)) s).2.2.2.2 (l ^ r) (pow_dvd_pow l (Nat.le_succ r)))
  have hred : ∀ n r s, unitsLevelToPrimePowReduction l n r (N * N) (cycM (topM l n r (N * N)) s)⁻¹ = κ r s := by
    intro n r s
    rw [map_inv, hκ, (hZc Ω l r s).1]
    exact congrArg (·⁻¹) ((hcy (topM l n r (N * N)) s).2.2.2.2 (l ^ r)
      (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)))
  have htop : ∀ n r, TopCoc X l N (2 * e - 1) n (topM l n r (N * N)) (zz n r) := fun n r =>
    topCocycle_finsetSum hA hI X l N _ n _ Finset.univ _ fun r₀ _ => hT Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  have hcr : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (GlobalTheory.KA.push (unitsPowPrimeReduction l r) (Z n (r + 1))) (Z n r) := by
    intro n r
    rw [hZeq, hZeq, unitsReduction_coe, pushforward_finsetSum]
    exact cocycleBound_finsetSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNr Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  have hcn : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (Z (n + 1) r) (Z n r) := by
    intro n r
    rw [hZeq, hZeq]
    exact cocycleBound_finsetSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNn Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  obtain ⟨YB, hYB, hcoc, hcont, hcomp, hlast⟩ := hc₁ c₀ hc₀ (fun r => (ZMod (l ^ r))ˣ) (fun r => unitsPowPrimeReduction l r) κ
    (fun n r => topM l n r (N * N)) (fun n r => unitsLevelToPrimePowReduction l n r (N * N)) (fun _ _ => 1) zz Z (fun r => unitsReduction_surjective l r) hπκ hred
    (fun _ _ _ _ => rfl) htop hcr hcn
  let prA : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  have hprA : ∀ b, prA b = pr b := fun _ => rfl
  have hpush : ∀ {B A' : Type} [Fintype B] [DecidableEq A'] (π : B → A') (f : (Ω ≃ₐ[ℚ] Ω) → B → X.Fn l) s y,
      pr (GlobalTheory.KA.push π f s y) = GlobalTheory.KA.push π (fun s y => pr (f s y)) s y := by
    intro B A' _ _ π f s y
    exact map_sum prA _ _
  have hln : ∀ n d, d ∈ X.B N l (2 * e - 1) → ∀ i, ‖pr ((l : ℤ_[l]) ^ n • d) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n d hd i
    have e1 : algebraMap ℚ_[l] (Qbar l) (((l : ℤ_[l]) ^ n : ℤ_[l]) : ℚ_[l]) = ((l : ℕ) : Qbar l) ^ n := by simp
    rw [hsm, e1, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_coefficient_ring cf (hint d hd i))
  have hfix : ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ),
      (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
    intro M _ s y
    have h1 : cycM M (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((hcy M 1).2.2.2.1).1 (one_mem _)
    have h2 : cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y = 1 := by
      have := (hcy M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹).2.1 (repM M y)
      rwa [inv_mul_cancel, h1, (hcy M s).2.2.1 y, eq_comm] at this
    rw [(hcy M _).2.2.2.1, (hcy M _).2.1, (hcy M _).2.1, (hcy M s).2.2.1]
    calc cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * cycM M s * (y * (cycM M s)⁻¹)
        = (cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y) * (cycM M s * (cycM M s)⁻¹) := by ac_rfl
      _ = 1 := by rw [h2, mul_inv_cancel, one_mul]
  refine ⟨fun r s y => pr (YB r s y), fun r n => ?_, fun r s s' y => ?_, fun r => ?_, fun r y i => ?_,
    fun r s u i => hint _ (hYB r s u) i⟩
  · obtain ⟨bB, hbB, b, hb, h⟩ := hlast r n
    refine ⟨bB, fun σ hσ => ?_, fun y => pr (b y), fun y i => hint _ (hb y) i, fun s y i => ?_⟩
    · rw [clsBmu_eq, hk]
      exact hbB σ hσ
    · obtain ⟨dd, hdd, hde⟩ := h s y
      rw [mul_one] at hde
      have hf : (fun s y => pr (shB X l (topM l n r (N * N)) bB s y)) = fun s y =>
          rhoK W e ψ (repM (topM l n r (N * N)) y) *ᵥ pr (bB ((repM (topM l n r (N * N)) y)⁻¹ * s *
            repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹))) := by
        funext s y
        exact heq _ _ (hbB _ (hfix _ s y)).1
      have hsh : pr (GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) =
          YfB X l pr W e ψ n r N bB s y := by
        rw [hpush, hf]
        rfl
      have hdec : YB r s y = GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y +
          (X.galB l s (b (y * κ r s)) - b y) + (l : ℤ_[l]) ^ n • dd := by
        rw [← hde]; abel
      have hprY : pr (YB r s y) = YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ pr (b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) - pr (b y)) + pr ((l : ℤ_[l]) ^ n • dd) := by
        rw [hdec, hadd, hadd, ← hprA (_ - _), map_sub, hprA, hprA, heq _ _ (hb _), hsh]
        rfl
      change ‖pr (YB r s y) i - (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ pr (b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) - pr (b y))) i‖ ≤ _
      have e3 : ∀ a b : Fin 2 → Qbar l, (a + b) i - a i = b i := fun a b => by simp
      rw [hprY, e3]
      exact hln n dd hdd i
  · change pr (YB r (s * s') y) = pr (YB r s y) + rhoK W e ψ s *ᵥ pr (YB r s' (y * κ r s))
    rw [hcoc, hadd, heq _ _ (hYB _ _ _)]
  · funext s y
    change pr (YB r s y) = GlobalTheory.KA.push (redL l r) (fun s y => pr (YB (r + 1) s y)) s y
    rw [hcomp r]
    exact hpush _ _ s y
  · rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε' hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_nat_cast_prime_lt_one_padic_closure l)
    rw [← norm_pow] at hn
    filter_upwards [hcont r n s y] with t ht
    obtain ⟨dd, hdd, hde⟩ := ht
    rw [dist_eq_norm]
    have e1 : pr (YB r t y) i - pr (YB r s y) i = pr ((l : ℤ_[l]) ^ n • dd) i := by
      rw [← hde, ← hprA (_ - _), map_sub, hprA, hprA]
      rfl
    rw [e1]
    exact lt_of_le_of_lt (hln n dd hdd i) hn
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

theorem UpperTheory.Kd.K4.ml :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
      (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
      (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
      (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
      ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ →
      ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ hc hl he _ hA
  obtain ⟨c₁, h⟩ := UpperTheory.Kd.K4.mlOf2 UpperTheory.V.Z.Kato.Sym.symEx UpperTheory.V.Z.Kato.Nb.sApi UpperTheory.V.Z.Kato.Nb.sInvApi UpperTheory.V.Z.Kato.Nb.sBStab
    UpperTheory.V.Z.Kato.Nb.sSlD UpperTheory.V.Z.Kato.Nb.sCohApi UpperTheory.V.Z.Kato.Nb.sCycZ UpperTheory.V.Z.Kato.Nb.sTop0 UpperTheory.V.Z.Kato.Nb.kato_norm_compatible_cyclotomic_tower
    UpperTheory.V.Z.Kato.Nb.katoZetaElement_normCompatible_in_lTower l Ω ε X N e hc hl he
  exact ⟨c₁, fun c₀ h₀ => h c₀ h₀ ι gN A W pr x c d gm ψ cf hA⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

theorem g3 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l),
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  AdmWn ι e gN A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
  ∃ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
    (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
    (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf hφ hgm hcop hl2 he hcw hadm _hWc _hWO
  obtain ⟨x₀, hx₀⟩ := hcw
  have h3 : ∀ x : ZMod N, AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf := fun x => hadm.1 x₀ hx₀
  have hml := fun x : ZMod N => UpperTheory.Kd.K4.ml l Ω ι e gN A W ε X pr N x c d gm ψ cf hgm hcop hl2 he hφ (h3 x)
  choose c₁ hc₁ using hml
  let C : ℕ := Finset.univ.sup c₁
  have hC : ∀ x, c₁ x ≤ C := fun x => Finset.le_sup (f := c₁) (Finset.mem_univ x)
  have hY := fun x : ZMod N => hc₁ x C (hC x)
  choose Yx hZ hS hP hCt hO using hY
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.K4.shCoc_wsum_props l Ω (rhoK W e ψ) cf (ZMod N) cw Yx hS hP hCt hO hadm.2
  refine ⟨C, fun r s y => ∑ x, cw x • Yx x r s y, ⟨Yx, hZ, fun r s y => rfl⟩, k1, k2, k3, k4⟩

end UpperTheory.Kd.K4

namespace UpperTheory.Kd.K4.ZetaTop

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]



theorem isZWc_raise {X : Tower Ω ε} {pr : X.Fn l → Fin 2 → Qbar l} {W : R2 Ω l} {e : ℕ} {ψ : ZMod l → Qbar l}
    {N : ℕ} [NeZero N] {cw : ZMod N → Qbar l} {c d k : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} {cf : Coef l} {c₀ : ℕ}
    {Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l} (m : ℕ)
    (hadd : ∀ b b', pr (b + b') = pr b + pr b')
    (hsm : ∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b)
    (h : IsZWc X l pr W e ψ N cw c d k gm cf c₀ Y) :
    IsZWc X l pr W e ψ N cw c d k gm cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  obtain ⟨Yx, hY, hsum⟩ := h
  refine ⟨fun x r s y => ((l : Qbar l) ^ m) • Yx x r s y,
    fun x => GlobalTheory.K4.zetaSystem_exponent_raise_of_prime_pow_smul l Ω ε X pr W e ψ N x c d k gm cf c₀ m (Yx x) hadd hsm (hY x), ?_⟩
  intro r s y
  simp only
  rw [hsum r s y, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_comm]

theorem shCoc_smul {Γ X R : Type*} [Group Γ] [Monoid X] [CommRing R] {ρ : Γ → Matrix (Fin 2) (Fin 2) R} {κ : Γ →* X}
    {Y : Γ → X → Fin 2 → R} (a : R) (h : ShCoc ρ κ Y) : ShCoc ρ κ (fun s y => a • Y s y) := by
  intro s t x
  simp only [h s t x, smul_add, Matrix.mulVec_smul]

theorem push_smul {Γ X X' R : Type*} [Fintype X'] [DecidableEq X] [CommRing R] (π : X' → X)
    (Y : Γ → X' → Fin 2 → R) (a : R) :
    GlobalTheory.KA.push π (fun s y => a • Y s y) = fun s y => a • GlobalTheory.KA.push π Y s y := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.smul_sum]

theorem spec_smul {Γ X R : Type*} [Fintype X] [CommRing R] (η : X → R) (Y : Γ → X → Fin 2 → R) (a : R) (s : Γ) :
    GlobalTheory.KA.spec η (fun s y => a • Y s y) s = a • GlobalTheory.KA.spec η Y s := by
  simp only [GlobalTheory.KA.spec, Finset.smul_sum, smul_comm a]

theorem exists_finset_unif [IsAlgClosure ℚ Ω] {T Q : Type} [Finite T] [SeminormedAddCommGroup Q]
    (f : (Ω ≃ₐ[ℚ] Ω) → T → Q) (hf : ∀ x, Continuous fun s => f s x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (x : T), (∀ z ∈ E0, s' z = z) → ‖f (s * s') x - f s x‖ ≤ δ := by
  classical
  haveI := Fintype.ofFinite T
  have hU : ∀ x, ∀ᶠ s' in nhds (1 : Ω ≃ₐ[ℚ] Ω), ∀ s ∈ (Set.univ : Set (Ω ≃ₐ[ℚ] Ω)),
      ‖f (s * s') x - f s x‖ < δ := by
    intro x
    refine isCompact_univ.eventually_forall_of_forall_eventually fun s _ => ?_
    have hc : Continuous fun z : (Ω ≃ₐ[ℚ] Ω) × (Ω ≃ₐ[ℚ] Ω) => ‖f (z.2 * z.1) x - f z.2 x‖ :=
      (((hf x).comp (continuous_snd.mul continuous_fst)).sub ((hf x).comp continuous_snd)).norm
    have h0 : ‖f (s * 1) x - f s x‖ < δ := by simpa using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds h0)
  have hV : {s' : Ω ≃ₐ[ℚ] Ω | ∀ x, ∀ s, ‖f (s * s') x - f s x‖ < δ} ∈ nhds (1 : Ω ≃ₐ[ℚ] Ω) := by
    have := Filter.eventually_all.2 hU
    filter_upwards [this] with s' hs' x s using hs' x s (Set.mem_univ _)
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hV
  have hfg : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    (Submodule.fg_iff_finiteDimensional _).2 hEfin
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun s s' x hfix => ?_⟩
  have hmem : s' ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ Subalgebra.toSubmodule E.toSubalgebra := hy
    rw [← ht] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => exact hfix z hz
    | zero => exact map_zero s'
    | add u v _ _ hu hv => rw [map_add, hu, hv]
    | smul a u _ hu => rw [map_smul, hu]
  exact (hEsub hmem x s).le

end UpperTheory.Kd.K4.ZetaTop

namespace UpperTheory.Kd.K4

open UpperTheory.Kd.K4.ZetaTop

theorem top : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
    (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
    ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
      (y : G ℚ Ω → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
      (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
      (∀ r y i, Continuous fun s => Y r s y i) ∧
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
      (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
      Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
      IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
      SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s) := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc ε X pr N _ cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  classical
  obtain ⟨c₀, Y, hZ, hSh, hPush, hCont, hO⟩ :=
    g3 l Ω ι e g A W ε X pr N cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  obtain ⟨x₀, hx₀⟩ := hcw
  obtain ⟨-, -, -, -, hadd, hsm, -⟩ := hAdm.1 x₀ hx₀
  obtain ⟨θ, hθc, hmatθ, hρO, hχO, hχcong, hηtw, hθIne, hDec, hη⟩ :=
    GlobalTheory.K4.twist_clauses l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hl2 ⟨x₀, hx₀⟩ hAdm
  obtain ⟨k, S', hIne, hfam⟩ := UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hmat hgm hlN
    hl2 he ⟨x₀, hx₀⟩ hφ hAdm c₀ Y hZ
  set Y' : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
    fun r s y => ((l : Qbar l) ^ k) • Y r s y with hY'
  have hlk : ((l : Qbar l) ^ k) ∈ cf.O := pow_mem (natCast_mem _ _) _
  have hSh' : ∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y' r) :=
    fun r => shCoc_smul _ (hSh r)
  have hCont' : ∀ r y i, Continuous fun s => Y' r s y i := by
    intro r y i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact continuous_const.mul (hCont r y i)
  have hO' : ∀ r s u i, Y' r s u i ∈ cf.O := by
    intro r s u i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact mul_mem hlk (hO r s u i)
  have hPush' : ∀ r, Y' r = GlobalTheory.KA.push (redL l r) (Y' (r + 1)) := by
    intro r
    simp only [hY']
    rw [push_smul, ← hPush r]
  obtain ⟨m, y, S'', hy, hSys, hIw, hSp⟩ :=
    GlobalTheory.KZ.middle_glue2 l Ω W cf A e S' (chiK l (Function.update ψ 0 0)) θ (rhoK W e ψ) (nuD W e ψ) Y'
      hWc hθc hmat hmatθ (hρO cf hmat) (hχO cf) hχcong hηtw hSh' hCont' hO'
      (fun r s => congrFun (hPush' r) s) hDec hIne hθIne (by
        intro n hn w hw hdvd ψw hk hs
        obtain ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfam n hn w hw hdvd ψw hk hs
        refine ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
        intro r s i
        rw [hη r]
        simp only [hY', spec_smul]
        exact h8 r s i)
  refine ⟨c₀ + k, m, cf, S'', Y', y, isZWc_raise k hadd hsm hZ, hSh', hPush', hCont', ?_, hO',
    fun z hz => hz, ?_, hSys, hIw, ?_⟩
  · intro r n
    have hpos : (0 : ℝ) < ‖((l : Qbar l) ^ n)‖ := by
      rw [norm_pos_iff]
      exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    obtain ⟨E0, hE0⟩ := exists_finset_unif (fun s y => Y' r s y 1) (fun y => hCont' r y 1) hpos
    exact ⟨E0, fun s s' y hfix => hE0 s s' y hfix⟩
  · intro r s i
    have := hy r s i
    rw [hη r] at this
    exact this
  · intro n
    obtain ⟨r₀, hr⟩ := hSp n
    refine ⟨r₀, fun r hr' s hs hc => ?_⟩
    have := hr r hr' s hs hc
    rwa [hη r] at this

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.kato_eulerSystem_integrality : UpperTheory.V.Z.Kato.Joint.KatoEulerSystemIwasawaClassStatement := UpperTheory.Kd.K4.top
end
