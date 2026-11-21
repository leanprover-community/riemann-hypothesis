import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurComponentsSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjChrEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

variable {D : D7}

theorem not_mem_of_offS {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSb : IsBadSet D Sb)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D Sb P) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro h
  have h1 : P.under (𝓞 D.host.F) ∈ Sb := (hSb _).2 (by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
    rwa [map_natCast])
  obtain ⟨x, hx, hy⟩ := hP _ h1
  exact hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl hx

theorem mem_of_typePlace {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsTypePlaces D.host.g pb Pg) {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ Pg) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  rw [h.2, Formalism.L2.DIV.mem_primesOf] at hPP
  obtain ⟨c₀, h₀⟩ := GlobalTheory.LevSplit.exists_conj (pb 0)
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LevSplit.exists_conj (pb 1)
  have e : ∀ i (c : 𝓞 D.host.E), (c : D.host.E) = star (pb i : D.host.E) → (D.host.g i : 𝓞 D.host.E) = pb i * c := by
    intro i c hc
    apply RingOfIntegers.coe_injective
    rw [map_natCast, map_mul, ← h.1.norm i, ← hc]
  rw [Nat.cast_mul, e 0 c₀ h₀, e 1 c₁ h₁, mul_mul_mul_comm]
  exact PP.asIdeal.mul_mem_right _ hPP.2

theorem sep_of_offS {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSb : IsBadSet D Sb)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D Sb P)
    {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsTypePlaces D.host.g pb Pg) {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ Pg) :
    PP ≠ P ∧ ¬ IsConjPl PP P := by
  have h1 := not_mem_of_offS hSb hP
  have h2 := mem_of_typePlace h hPP
  refine ⟨fun e => h1 (e ▸ h2), fun hc => ?_⟩
  obtain ⟨c, hc, e⟩ := hc _ h2
  have : c = ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_natCast]
    refine e.trans ?_
    rw [show (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _, star_natCast]
  exact h1 (this ▸ hc)

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]


end GlobalTheory.HeckeKeepsGood
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem iSup_partH_eq_top_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hS
  classical
  obtain ⟨hinj, hrange, -⟩ := hC.models.HW i σ
  have hrange' : LinearMap.range (R.HW i σ).e =
      Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i) := hrange
  haveI : FiniteDimensional ℂ
      (Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i)) := by
    rw [← hrange']; infer_instance
  obtain ⟨n, hB⟩ := hC.lev.βW i
  have key := mult_le_of_parts (J := Lev.levG _ (R.βW i) (R.datWp i R.triv)) (Sb := GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R)
    hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 hS (fun P d Rp h T hT => ?_)
    ((⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c).map (R.HW i σ).e) (fun c hc T hT => ?_)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := key (hrange' ▸ LinearMap.mem_range_self _ x)
    exact hinj e ▸ hy
  · have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [one_pow, Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
    have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
      obtain ⟨_, _, _, _, hO, -⟩ := h
      exact hO
    have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
      rintro PP (hP | hP)
      · exact GlobalTheory.HeckeOffLevel.sep_of_offS hO (by
          unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
          exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
      · exact absurd hP (Finset.notMem_empty _)
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => GlobalTheory.HeckeOffLevel.hasType_heckeLin hB hN hP h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  · obtain ⟨y, rfl⟩ : T ∈ LinearMap.range (R.HW i σ).e := hrange' ▸ hT.1
    exact Submodule.mem_map_of_mem
      (le_iSup₂_of_le (f := fun (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c) => partH R i σ c) c hc le_rfl hT)

end GlobalTheory.PrincipalDecomp

namespace GlobalTheory.LiftLower

theorem gW_mem_partH_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ c g x hx
  unfold partH at hx ⊢
  rw [Submodule.mem_comap, mem_partFull] at hx ⊢
  refine ⟨?_, fun P d Rp hR v => ?_⟩
  · have h : (R.HW i σ).e (R.gW i σ g x) ∈ LinearMap.range (R.HW i σ).e := LinearMap.mem_range_self _ _
    rw [(hC.models.HW i σ).2.1] at h
    exact h
  have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  obtain ⟨-, h2⟩ := GlobalTheory.offS_not_type_places R.C.P R.Pg (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P hC.lev.Pg
    (fun PP hPP => by unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF; exact Finset.mem_image.2 ⟨PP, hPP, rfl⟩) hO
  obtain ⟨a, hB⟩ := hC.lev.βW i
  have hN : (((1 ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
  have hPP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    rintro PP (h | h)
    · exact h2 PP h
    · exact absurd h (Finset.notMem_empty _)
  have hT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 hx.1).lev v
  rw [hC.models.gW i σ g x, postOn_apply, ← map_smul, ← hx.2 P d Rp hR v]
  exact (GlobalTheory.HeckeKeepsGood.sphericalOperator_commute_levelFiniteGroup hB hN hPP hR hT (R.eG g)).symm

end GlobalTheory.LiftLower

namespace GlobalTheory.ConjMuChar

theorem exists_galConj_chrEq_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ s hσ μ' hμ
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add, RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hC.lev.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hC.lev.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

end GlobalTheory.ConjMuChar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

theorem exists_galConj_eta_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar

namespace GlobalTheory.FiveClauseParts

theorem parts_conj_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) :=
  ⟨GlobalTheory.PrincipalDecomp.iSup_partH_eq_top_five, GlobalTheory.LiftLower.gW_mem_partH_five,
    GlobalTheory.ConjMuChar.exists_galConj_chrEq_five, GlobalTheory.EtaConjChar.exists_galConj_eta_five⟩

end GlobalTheory.FiveClauseParts

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) := by
  atlas_forward_decl GlobalTheory.FiveClauseParts.parts_conj_five
end
