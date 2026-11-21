import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.ThmAMove

section Val

variable {K : Type} [Field K] (A : ValuationSubring K)

theorem exists_ext {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [IsAlgClosed K] (jk : FractionRing R →+* K) :
    ∃ je : FractionRing S →+* K, ∀ x, je (IsFractionRing.map (j := algebraMap R S) hinj x) = jk x := by
  let k : FractionRing R →+* FractionRing S := IsFractionRing.map (j := algebraMap R S) hinj
  letI : Algebra (FractionRing R) (FractionRing S) := k.toAlgebra
  letI : Algebra (FractionRing R) K := jk.toAlgebra
  have hi : ∀ a : S, IsIntegral (FractionRing R) (algebraMap S (FractionRing S) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap R (FractionRing R)) (algebraMap S (FractionRing S))
      (RingHom.ext fun r => by
        show k (algebraMap R _ r) = _
        simp [k, IsFractionRing.map]) (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    rw [div_eq_mul_inv]
    exact ((hi a).mul (hi b).inv).isAlgebraic⟩
  let j : FractionRing S →ₐ[FractionRing R] K := IsAlgClosed.lift
  exact ⟨j.toRingHom, fun x => j.commutes x⟩

theorem exists_unit {S : Type} [CommRing S] [IsDomain S] [ValuationRing S] (je : FractionRing S →+* K)
    (hA : ∀ a : S, je (algebraMap S _ a) ∈ A) (hu : ∀ a : S, A.valuation (je (algebraMap S _ a)) = 1 → IsUnit a)
    {x y : FractionRing S} (h : A.valuation (je x) = A.valuation (je y)) : ∃ u : Sˣ, x = algebraMap S _ (u : S) * y := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨1, ?_⟩
    simpa using h
  have hy' : A.valuation (je y) ≠ 0 := by simpa using hy
  have h1 : A.valuation (je (x / y)) = 1 := by rw [map_div₀, map_div₀, h, div_self hy']
  rcases ValuationRing.isInteger_or_isInteger S (x / y) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, h1])
    exact ⟨u, by rw [ha, div_mul_cancel₀ _ hy]⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, map_inv₀, map_inv₀, h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, ha, inv_inv, div_mul_cancel₀ _ hy]

theorem mem_max_iff {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : R →+* K) (hf : ∀ r, f r ∈ A) {l : ℕ}
    (hl0 : (l : K) ≠ 0) (hl : A.valuation (l : K) < 1) (a : R) :
    a ∈ IsLocalRing.maximalIdeal R ↔ A.valuation (f a) < 1 := by
  have hle : ∀ r, A.valuation (f r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hf r)
  constructor
  · intro ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have h0 : (l : R) ≠ 0 := fun h => hl0 (by rw [← map_natCast f, h, map_zero])
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    have hd : (l : R) ∣ a ^ n := by
      rw [hn, Units.mul_left_dvd]
      exact pow_dvd_pow_of_dvd ha n
    obtain ⟨c, hc⟩ := hd
    refine lt_of_le_of_ne (hle a) fun h1 => ?_
    have h2 := congrArg (fun r => A.valuation (f r)) hc
    simp only [map_pow, map_mul, map_natCast, h1, one_pow] at h2
    exact absurd h2 (mul_lt_one_of_lt_of_le hl (hle c)).ne'
  · intro h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h2 : A.valuation (f u) * A.valuation (f (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_lt_of_le h (hle _)).ne

variable {L : Type} [Field L] [NumberField L]

theorem int_le_one (β : L →+* K) (x : 𝓞 L) : A.valuation (β x) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  have h : IsIntegral A (β x) := IsIntegral.map_of_comp_eq (Int.castRingHom A) β (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact hy ▸ y.2

theorem unit_of_centre (β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) (h : ∀ x : 𝓞 L, A.valuation (β x) < 1 ↔ x ∈ P.asIdeal)
    (y : L) (hy : P.valuation L y = 1) : A.valuation (β y) = 1 := by
  obtain ⟨n, d, e⟩ := P.exists_primeCompl_mul_eq_of_integer y hy.le
  have h1 : ∀ x : 𝓞 L, x ∉ P.asIdeal → A.valuation (β x) = 1 := fun x hx =>
    le_antisymm (int_le_one A β x) (not_lt.1 fun h' => hx ((h x).1 h'))
  have hd : P.valuation L (algebraMap (𝓞 L) L d) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 d.2
  have hn : n ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show P.valuation L (algebraMap (𝓞 L) L n) = 1
    rw [← e, map_mul, hy, hd, one_mul]
  have h2 := congrArg (fun r => A.valuation (β r)) e
  simp only [map_mul] at h2
  rw [show A.valuation (β (algebraMap (𝓞 L) L d)) = 1 from h1 _ d.2, show A.valuation (β (algebraMap (𝓞 L) L n)) = 1 from h1 _ hn,
    mul_one] at h2
  exact h2

theorem val_eq_of_unit (α β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) {l : ℕ} (hl0 : l ≠ 0) (hl : P.valuation L (l : L) ≠ 1)
    (hα : ∀ y, P.valuation L y = 1 → A.valuation (α y) = 1) (hβ : ∀ y, P.valuation L y = 1 → A.valuation (β y) = 1) (x : L) :
    A.valuation (α x) = A.valuation (β x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hl1 : (l : L) ≠ 0 := Nat.cast_ne_zero.2 hl0
  have e1 : P.valuation L x = WithZero.exp (WithZero.log (P.valuation L x)) := (WithZero.exp_log (by simpa using hx)).symm
  have e2 : P.valuation L (l : L) = WithZero.exp (WithZero.log (P.valuation L (l : L))) :=
    (WithZero.exp_log (by simpa using hl1)).symm
  generalize WithZero.log (P.valuation L x) = n at e1
  generalize WithZero.log (P.valuation L (l : L)) = e at e2
  have he : e ≠ 0 := by
    rintro rfl
    exact hl e2
  have hy : P.valuation L (x ^ e * (l : L) ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, map_zpow₀, e1, e2, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [mul_comm]
  have h1 := (hα _ hy).trans (hβ _ hy).symm
  simp only [map_mul, map_zpow₀, map_natCast] at h1
  have h0 : A.valuation (l : K) ^ (-n) ≠ 0 := zpow_ne_zero _ (by
    rw [← map_natCast α, map_ne_zero, map_ne_zero]; exact hl1)
  exact (zpow_left_inj₀ zero_le' zero_le' he).1 (mul_right_cancel₀ h0 h1)

theorem exists_aut_centre [IsGalois ℚ L] (L0 : IntermediateField ℚ L) (β : L →+* K) (P : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L0, A.valuation (β ((x : L0) : L)) < 1 ↔ algebraMap (𝓞 L0) (𝓞 L) x ∈ P.asIdeal) :
    ∃ σ : L ≃ₐ[L0] L, ∀ x : 𝓞 L, A.valuation (β (σ x)) < 1 ↔ x ∈ P.asIdeal := by
  let f : 𝓞 L →+* A := (β.comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (int_le_one A β x)
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP' : ∀ x : 𝓞 L, x ∈ P' ↔ A.valuation (β x) < 1 := fun x => A.valuation_lt_one_iff (f x)
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI := P.isPrime
  haveI : P'.LiesOver (P.asIdeal.under (𝓞 L0)) := ⟨Ideal.ext fun x => ((hP' (algebraMap (𝓞 L0) (𝓞 L) x)).trans (h x)).symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.asIdeal.under (𝓞 L0)) P.asIdeal P' (L ≃ₐ[L0] L)
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, hP']
  rfl

end Val

theorem exists_symbol {K Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (σ : Formalism.ConjugateSelfDual.G K Ω) :
    ∃ t, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ := by
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω σ)⁻¹
  let t : (Af K)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing K) (Af K)) x
  let y : (InfiniteAdeleRing K)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing K) (Af K)) x
  have hy : y ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ := by
    let T : Set (InfiniteAdeleRing K) := Set.univ.pi fun w => {0}ᶜ
    have hS : ∀ w : InfinitePlace K, IsPreconnected ({0}ᶜ : Set w.Completion) := fun w => by
      have hw := IsTotallyComplex.isComplex w
      have := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
        (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected
      convert this using 1
      ext z
      exact (map_ne_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)).symm
    have hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T) := by
      rw [← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
      · exact isPreconnected_univ_pi hS
      · intro y hy
        have : IsUnit y := Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ (hy w trivial)
        exact this
    have hm : ∀ u : (InfiniteAdeleRing K)ˣ, u ∈ (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T :=
      fun u w _ => (Pi.isUnit_iff.1 u.isUnit w).ne_zero
    exact hp.subset_connectedComponent (hm 1) (hm y)
  let y' : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (Af K)) y
  have h1 : art y' = 1 := by
    rw [← MonoidHom.mem_ker, ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
  have e : x = y' * finIdele K t := by
    ext : 1
    apply Prod.ext
    · show _ = _ * 1
      rw [mul_one]; rfl
    · show _ = 1 * _
      rw [one_mul]; rfl
  refine ⟨t, ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol, inv_eq_iff_eq_inv, ← hx]
  conv_rhs => rw [e, map_mul, h1, one_mul]

theorem exists_exponent {G : Type} [CommGroup G] (ψ : G →* ℂˣ) {l n : ℕ} (hl : l.Prime) (h : ∀ q, ψ q ^ l ^ n = 1) (g : ℂ ≃+* ℂ)
    {c : ℤ} (hc : IsCoprime c (l : ℤ)) :
    ∃ a : ℤ, IsCoprime a (l : ℤ) ∧ (Units.map g.toRingHom.toMonoidHom).comp ψ = ψ ^ (c * a) := by
  have hN : l ^ (n + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨hN⟩
  have hζ := Complex.isPrimitiveRoot_exp _ hN
  generalize Complex.exp _ = ζ at hζ
  have hg : IsPrimitiveRoot (g ζ) (l ^ (n + 1)) := hζ.map_of_injective g.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hec : e.Coprime (l ^ (n + 1)) := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero hN) e).1 (he ▸ hg)
  have hel : IsCoprime (e : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff n.succ_pos _ _).1 hec)
  obtain ⟨u, v, huv⟩ : IsCoprime c ((l : ℤ) ^ (n + 1)) := hc.pow_right
  have hu : IsCoprime u (l : ℤ) := ⟨c, v * l ^ n, by rw [← huv]; ring⟩
  refine ⟨u * e, hu.mul_left hel, MonoidHom.ext fun q => ?_⟩
  have h1 : ψ q ^ l ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, h, one_pow]
  have h2 : ψ q ^ (c * (u * e)) = ψ q ^ e := by
    rw [show c * (u * e) = e + ((l ^ (n + 1) : ℕ) : ℤ) * (-(v * e)) by push_cast; linear_combination (e : ℤ) * huv, zpow_add,
      zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (ψ q : ℂ)) (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  refine Eq.trans (Units.ext ?_) h2.symm
  show g (ψ q : ℂ) = _
  rw [Units.val_pow_eq_pow_val, ← hk, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols in

theorem ratio_conj (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : ToricRatioConjugates)
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] [Nonempty I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (h1 : UnramFin E) (h2 : Module.finrank ℚ K = 2) (h3 : 0 < d) (h4 : δ ^ 2 = -(d : K))
    (h5 : IsCMType φ) (h6 : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (h7 : 1 ≤ s) (h8 : ∀ i, 1 ≤ κ i) (h9 : IsBaseCond 𝔣) (h10 : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h11 : IsValChar φ s κ 𝔣 ∅ χ)
    {T₀ : ℂ} {T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ} (hT₀ : IsToricSum φ s κ 𝔣 χ T₀)
    (hT : ∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) (g : ℂ ≃+* ℂ)
    (hφ : ∀ i x, g (φ i x) = φ i x) (hχ : ∀ y, g (lamF χ s y) = lamF χ s y) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) :
    ∃ ζ : ℂˣ, IsOfFinOrder ζ ∧ g (T ψ / T₀) = (ζ : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) := by
  obtain ⟨T₀', T', a1, -, a2, -, a3⟩ := hG E K d δ ι I φ s κ 𝔣 Q χ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain rfl : T₀' = T₀ := a1.unique hT₀
  obtain rfl : T' = T := funext fun ψ => (a2 ψ).unique (hT ψ)
  haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by
    have h := congrArg (InfinitePlace.embedding_of_isReal hw) h4
    rw [map_pow, map_neg, map_natCast] at h
    have : (0 : ℝ) < d := by exact_mod_cast h3
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw δ)]⟩
  let Ω := AlgebraicClosure K
  letI : Algebra K ℂ := ι.toAlgebra
  let j : Ω →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← h6 (Classical.arbitrary I)]
    exact hφ _ _
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨art, ha⟩ := hA K Ω
  obtain ⟨t, ht⟩ := exists_symbol ha (gK.restrictNormal Ω)
  obtain ⟨b1, b2⟩ := a3 Ω j.toRingHom art (RingHom.ext j.commutes) ha g _ t hφ hχ (gK.restrictNormal_commutes Ω) ht ψ
  exact ⟨_, b2, b1⟩

end GlobalTheory.ThmAMove
end
end

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmAMove

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems

variable {D : D7}

private theorem val_pos_iff (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    0 < D.what₂.places.val w y ↔ (D.plEq w).valuation D.what₂.LL y < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd, ← WithZero.log_lt_log h0 one_ne_zero, WithZero.log_one]
  norm_cast
  omega

private theorem val_zero_iff (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    D.what₂.places.val w y = 0 ↔ (D.plEq w).valuation D.what₂.LL y = 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd]
  norm_cast
  rw [neg_eq_zero]
  exact ⟨fun h => by rw [← WithZero.exp_log h0, h, WithZero.exp_zero], fun h => by rw [h, WithZero.log_one]⟩

private theorem val_resChar_lt (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
  rw [← val_pos_iff, D.what₂.places.val_resChar w]
  exact_mod_cast D.what₂.places.ramIdx_pos w

private theorem exists_place (C : NChoice D) (w w' : D.what₂.places.Pl) (hw' : LiesUnder D (C.twI w) w')
    (ι : ℂ →+* Kbar D.ntw (C.twI w))
    (hι : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
    (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
    (hjk : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))) :
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1) ∧
      (∀ x : D.LL0, g (D.what₂.embLL x) = D.what₂.embLL x) ∧
      ∀ y, (D.plEq w').valuation D.what₂.LL y = 1 → A.valuation (ι (g (D.what₂.embLL y))) = 1 := by
  haveI := C.Oe_fin w
  haveI := D.galLL
  obtain ⟨je, hje⟩ := exists_ext (C.Oe_inj w) jk
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing (je.comp (algebraMap (C.Oe w) (FractionRing (C.Oe w))))
  have hu : ∀ a : C.Oe w, A.valuation (je (algebraMap _ _ a)) = 1 → IsUnit a := fun a h =>
    hloc.1 a ((A.valuation_eq_one_iff ⟨_, hA a⟩).2 h)
  have hα : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1 := by
    have key : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) ≤ 1 := fun y hy => by
      obtain ⟨a, ha⟩ := (C.embW_w w y).1 ((val_zero_iff w y).2 hy).ge
      rw [← ha, A.valuation_le_one_iff]
      exact hA a
    intro y hy
    refine le_antisymm (key y hy) ?_
    have h1 := key y⁻¹ (by rw [map_inv₀, hy, inv_one])
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    rwa [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hy0))] at h1
  have hp := D.what₂.places.resChar_prime w
  have hl : A.valuation ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) < 1 := by
    refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 (natCast_mem A _)) fun h => ?_
    obtain ⟨u, hu'⟩ := hu ((D.what₂.places.resChar w : ℕ) : C.Oe w) (by rwa [map_natCast, map_natCast])
    have h1 : 0 ≤ D.what₂.places.val w (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹) :=
      (C.embW_w w _).2 ⟨(u⁻¹ : (C.Oe w)ˣ), by rw [map_units_inv, hu', map_inv₀, map_natCast, map_natCast]⟩
    have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h2 := (D.what₂.places.val w).map_mul ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)
      (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹)
    rw [mul_inv_cancel₀ hne, AddValuation.map_one] at h2
    exact absurd h2 (add_pos_of_pos_of_nonneg ((val_pos_iff w _).2 (val_resChar_lt w)) h1).ne
  have hl0 : ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) ≠ 0 := by
    rw [← map_natCast ι, map_ne_zero]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  let f0 : D.ntw.O0 (C.twI w) →+* Kbar D.ntw (C.twI w) := (toBar D.ntw (C.twI w)).comp (algebraMap _ _)
  have hf0 : ∀ r, f0 r ∈ A := fun r => by
    have e1 := GlobalTheory.ToricRational.toBar_algebraMap (X := D.ntw) (C.twI w) r
    have e2 := DFunLike.congr_fun hjk (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r))
    rw [RingHom.comp_apply, BlochKatoReduction.Gen.kMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← hje] at e2
    replace e2 := e2.trans e1.symm
    have e3 := hA (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) _ (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r)))
    show toBar D.ntw (C.twI w) (algebraMap _ _ r) ∈ A
    rw [← e2]
    simpa [IsFractionRing.map] using e3
  obtain ⟨σ, hσ⟩ := exists_aut_centre A D.LL0 (ι.comp D.what₂.embLL) (D.plEq w') fun x => by
    have hi : IsIntegral (D.ntw.O0 (C.twI w)) (D.ntw.emb0 (C.twI w) x) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (C.twI w)) (RingHom.ext_int _ _) x.isIntegral_coe
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have e1 : (ι.comp D.what₂.embLL) ((x : D.LL0) : D.what₂.LL) = f0 a := by
      rw [RingHom.comp_apply, hι, ← ha]; rfl
    rw [e1, ← mem_max_iff A f0 hf0 hl0 hl, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL), ← val_pos_iff]
    refine Iff.trans ⟨fun h => ⟨a, h, ha⟩, fun ⟨y, hy, e⟩ => ?_⟩ (hw' x)
    rwa [← IsFractionRing.injective _ (FractionRing (D.ntw.O0 (C.twI w))) (e.trans ha.symm)]
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨g, hg⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq D.what₂.embLL (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)
  refine ⟨je, A, g, hje, fun x y h => exists_unit A je hA hu h, hα, fun x => ?_, fun y hy => ?_⟩
  · rw [hg]
    exact congrArg D.what₂.embLL (σ.commutes x)
  · rw [hg]
    exact unit_of_centre A (ι.comp (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)) _ hσ y hy

private theorem exists_side (C : NChoice D) (w : D.what₂.places.Pl)
    (hw : LiesUnder D (C.twI w) w ∨ LiesUnder D (C.twI w) (D.what₂.places.conj w)) : ∃ b : Bool,
    ∀ (ι : ℂ →+* Kbar D.ntw (C.twI w))
      (_ : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
      (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
      (_ : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))),
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange, starRingEnd ℂ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange → g t = t) ∧
      ∀ z, A.valuation (je (C.embW w z)) = A.valuation (atSide D.ntw b ι (g (D.what₂.embLL z))) := by
  have hp := (D.what₂.places.resChar_prime w).ne_zero
  rcases hw with hw | hw
  · refine ⟨true, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place C w w hw ι hι jk hjk
    refine ⟨je, A, g, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w)) (ι.comp (g.toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt w).ne h3 h5⟩
    rintro _ ⟨x, rfl⟩ -
    exact h4 x
  · refine ⟨false, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place C w _ hw ι hι jk hjk
    let c : ℂ ≃+* ℂ := Complex.conjAe.toRingEquiv
    have hc : ∀ t, c t = starRingEnd ℂ t := fun _ => rfl
    refine ⟨je, A, (c.trans g).trans c, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w))
      ((atSide D.ntw false ι).comp (((c.trans g).trans c).toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt w).ne h3 fun y hy => ?_⟩
    · rintro t - ⟨x, hx⟩
      show c (g (c t)) = t
      rw [hc t, ← hx]
      refine (congrArg c (h4 x)).trans ?_
      show starRingEnd ℂ (Formalism.L2.Host.embLL0 D x) = t
      rw [hx, Complex.conj_conj]
    · letI := D.starLL
      have h6 := h5 (star y) (by rw [← val_zero_iff, D.conj_val, star_star, val_zero_iff, hy])
      rw [D.starLL_cx] at h6
      show A.valuation (ι (starRingEnd ℂ (starRingEnd ℂ (g (starRingEnd ℂ (D.what₂.embLL y)))))) = 1
      rwa [Complex.conj_conj]

private theorem emb_mem (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let _ : Algebra D.host.E ℂ := D.host.φ₀.toAlgebra
  have : IsScalarTower ℚ D.host.E ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast D.host.φ₀ q).symm
  have e : D.host.φ₀ (σ.toRatAlgHom.restrictNormal D.host.E x) = σ x := σ.toRatAlgHom.restrictNormal_commutes D.host.E x
  rw [← e, ← D.embE_φ₀]
  exact ⟨⟨_, D.hostField_le_fixedField _⟩, rfl⟩

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF}

private theorem almostIn (h : GridFit p G) (i j : Fin D.R.m) (l : ℕ) :
    GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) (nuH G p.P.A3.A.μ0 i j * p.R.C.delAt l) := by
  unfold nuH
  rw [GlobalTheory.ThmAUpper.xiH_base p, mul_one, div_eq_mul_inv]
  refine ((GlobalTheory.GalChar.almostIn_of_valuesIn (h.frame.mu0 j)).mul
    (GlobalTheory.GalChar.almostIn_of_valuesIn (h.field.values _ (by omega) (by omega))).inv).mul ?_
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del', GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del]

private theorem divisorProofs_isSet_fact (h : GridFit p G) {w : D.what₂.places.Pl} (hw : TwistedAt D w) :
    IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) (belowSet (ex.nch.Q w)) := by
  refine (placesBelow_splitCoprimeConductor_of_admissible (h.cond w hw) fun P hP => (h.list _ (h.setting.inW1 hw)).1 P ?_).1
  obtain ⟨v, hv, hd⟩ := (Prime.dvd_finset_prod_iff (below P).prime _).1 hP
  have e : below P = v := HeightOneSpectrum.ext
    ((v.isMaximal.eq_of_le (below P).isPrime.ne_top (Ideal.le_of_dvd ((below P).prime.dvd_of_dvd_pow hd))).symm)
  subst e
  rcases G.pl.mem_S0_of_sum_eq.1 hv with h0 | h1
  · refine Dvd.dvd.mul_left ?_ _
    have : below (G.pl.w G.pl.v0) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    show _ ∣ (below (G.pl.w G.pl.v0)).asIdeal
    rw [this, ← h0]
  · refine Dvd.dvd.mul_right (dvd_pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    have := (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1
    simp only [Nat.cast_mul, (below P).isPrime.mul_mem_iff_mem_or_mem, or_assoc]
    exact this

end Point

theorem _root_.GlobalTheory.T.toric_ratio_field_data_cm : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → ∀ z : D.what₂.LL, D.what₂.embLL z * T₀ = T ψc → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) →
      ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (a : ℤ) (u : (ex.nch.Oe w)ˣ), IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) ∧
        ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) =
          algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (u : ex.nch.Oe w) *
            ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
              (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z hz hread
  obtain ⟨hcm, -, hfd, hbc, -⟩ := hF
  obtain ⟨ι, hι, hread⟩ := hread
  obtain ⟨b, hb⟩ := exists_side ex.nch w (hfit.1.setting.1 w hw).2
  obtain ⟨lam, jk, c, -, hc, hjk, hid⟩ := hread b
  obtain ⟨je, A, g, h1, h2, h3, h4⟩ := hb ι hι jk hjk
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (GlobalTheory.FunObj.SqNum.cmPhi D) := hfd.2.2.2.2.2.2.1
  generalize hχ : nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) = χ at hv h0 hT'
  have hal : GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) χ := hχ ▸ almostIn hfit.1 i j _
  have hfin : Finite (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅)) := by
    rw [condQ, Finset.prod_empty, mul_one]; exact h0.1
  have hval : ∀ y, (finPart χ y : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange :=
    GlobalTheory.ToricRational.finPart_mem hv.2.2.1 (GlobalTheory.ToricRational.condQ_ne_bot hbc.1 ∅)
      (OrderUnits.finPart_eq_one _ _ _ hφ s _ _ ∅ χ hU hbc (fun _ h => absurd h (Finset.notMem_empty _)) hv) _ emb_mem
      (Filter.eventually_cofinite.1 hal).toFinset fun P hP => by simpa using hP
  have hlam : ∀ y, g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y := fun y => by
    have hm : ((modF y ^ s : ℝ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
      rw [Complex.ofReal_pow]
      exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
    refine h3 _ (mul_mem (hval y) hm) ?_
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, map_mul, Complex.conj_ofReal, ← Complex.inv_eq_conj (show ‖(finPart χ y : ℂ)‖ = 1 from hv.1 _)]
    exact mul_mem (inv_mem (hval y)) hm
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨ζ, hζ, hg⟩ := ratio_conj CompanionTheory.FamInh.globalArtin hG D.host.E D.host.K D.host.d δ _ _ _ s _ _ _ χ hU (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D)
    hfd.1.pos hδ hφ (fun τ => GlobalTheory.RowEx.RatioField.cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D 1 i j τ hs2).2) hbc (divisorProofs_isSet_fact hfit.1 hw) hv h0 hT' g
    (fun τ x => h3 _ (emb_mem _ x) (emb_mem ((starRingEnd ℂ).comp _) x)) hlam ψc
  obtain ⟨n, hn⟩ := (p.Tp.psi_is w hw).ord
  rw [ex.nch.twI_l] at hc ⊢
  obtain ⟨a, ha, he⟩ := exists_exponent ψc (n := n) (D.what₂.places.resChar_prime w) (fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← hψ]
    exact congrArg (fun ξ => finPart ξ y) hn) g hc
  have hid' := hid a
  rw [← he] at hid'
  have hz' : T ψc / T₀ = D.what₂.embLL z := by rw [← hz, mul_div_cancel_right₀ _ h0ne]
  have hT : T (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.conjChar g ψc) = ζ * g (D.what₂.embLL z) * T₀ := by
    rw [← hz', hg]
    field_simp
  have hζ1 : A.valuation (atSide D.ntw b ι ζ) = 1 := by
    obtain ⟨m, hm, hm'⟩ := isOfFinOrder_iff_pow_eq_one.1 hζ
    refine (pow_eq_one_iff_of_nonneg zero_le hm.ne').1 ?_
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hm', Units.val_one, map_one, map_one]
  obtain ⟨u, hu⟩ := h2 (ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)
      (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ))) (ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
      (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a)))) (by
    have e := hid'.trans (congrArg (fun t => _ * atSide D.ntw b ι t) hT)
    rw [map_mul, ← mul_assoc] at e
    have e' := mul_right_cancel₀ ((map_ne_zero _).2 h0ne) e
    rw [map_mul, h1, h1, e', map_mul, map_mul, map_mul, map_mul, hζ1, one_mul, h4, mul_comm])
  exact ⟨lam, a, u, ha, hu⟩

end GlobalTheory.ThmAMove
end
end
