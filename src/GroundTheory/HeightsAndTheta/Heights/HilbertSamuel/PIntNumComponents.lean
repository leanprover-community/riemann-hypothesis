import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntNumComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomogIdeal_map_coeff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    {P : Ideal (MRingOver R ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRingOver R ι →+* MRingOver S ι)) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine ⟨MvPolynomial.map φ '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset φ f hm) k⟩

theorem zcomb_fsH_a [Fintype K] (L : HermLine ι) (q p : ℕ) :
    (HermLine.zcomb L (fsH ι) q p).a = (q : ℤ) • L.a + fun _ => (p : ℤ) := by
  funext k
  simp [HermLine.zcomb, fsH, HermLine.ofMetrics]

theorem Perturb.proof (hGen : SmallGenTwist.Statement) (hSemi : SemiposTwist.Statement)
    (hDeg : GenDegTwist.Statement) (hFib : GenOnFibres.Statement) (hAmp : AmpleOfGenTwist.Statement) :
    Perturb.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D L P0 p q _ hV _ hL hp hq
  obtain ⟨n, w, hw, hgw, -⟩ := hL.gen
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  have hfib := hFib K ι Ω y L.a n w hw hgw
  refine ⟨⟨hL.normalForm_baseLattice_le_dualSpan_sup_line, hSemi K ι P0 _ L p q hL.semipos, ?_, hGen K ι Ω y L p q hL.gen⟩, ?_, ?_⟩
  · rw [zcomb_fsH_a]
    exact hDeg K ι Ω y D L.a n w p q hV hw hgw hL.deg_pos hq
  · rw [zcomb_fsH_a]
    exact hAmp ℚ K ι (KH.genIdeal y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) hfib.1 hp
  · intro ℓ hℓ
    have := Fact.mk hℓ
    rw [zcomb_fsH_a]
    exact hAmp (ZMod ℓ) K ι (fibreIdeal ℓ y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) (hfib.2 ℓ hℓ) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace IntNumComponents

theorem mem_minimalPrimes_iInf_iff {A : Type*} [CommRing A] {J₀ : Ideal A} {S : Finset (Ideal A)}
    (hS : ∀ W ∈ S, W ∈ J₀.minimalPrimes) (Z : Ideal A) :
    Z ∈ (⨅ W ∈ S, W).minimalPrimes ↔ Z ∈ S := by
  have hinf : (⨅ W ∈ S, W) = S.inf id := by rw [Finset.inf_eq_iInf]; rfl
  have key : ∀ Q : Ideal A, Q.IsPrime → (⨅ W ∈ S, W) ≤ Q → ∃ W ∈ S, W ≤ Q := by
    intro Q hQ hle
    rw [hinf] at hle
    exact hQ.inf_le'.mp hle
  constructor
  · intro hZ
    obtain ⟨W, hW, hWZ⟩ := key Z hZ.1.1 hZ.1.2
    have hZW : Z ≤ W := hZ.2 ⟨(hS W hW).1.1, iInf₂_le W hW⟩ hWZ
    rwa [le_antisymm hZW hWZ]
  · intro hZ
    refine ⟨⟨(hS Z hZ).1.1, iInf₂_le Z hZ⟩, fun Q hQ hQZ => ?_⟩
    obtain ⟨W, hW, hWQ⟩ := key Q hQ.1 hQ.2
    exact ((hS Z hZ).2 (hS W hW).1 (hWQ.trans hQZ)).trans hWQ

theorem isRadical_iInf {A : Type*} [CommRing A] {S : Finset (Ideal A)} (hS : ∀ W ∈ S, W.IsPrime) :
    (⨅ W ∈ S, W).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  simp only [Submodule.mem_iInf] at hn ⊢
  exact fun W hW => (hS W hW).mem_of_pow_mem n (hn W hW)

theorem multAt_toNat_of_isRadical {K : Type*} {ι : K → Type*} {J W : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    [W.IsPrime] (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) : (NumbersDVR.multAt J W).toNat = 1 := by
  have h1 := localMult_eq_one_of_isRadical hJ hW
  unfold localMult at h1
  rw [dif_pos ‹W.IsPrime›] at h1
  unfold NumbersDVR.multAt
  rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]
  exact h1

end IntNumComponents

open IntNumComponents in

theorem IntNumComponents.proof : IntNumComponents.Statement := by
  intro K _ _ ι _ P e a S hP hS
  have hJ₀h : NumbersDVR.IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) :=
    (Bridge.isMultiHomogIdeal_iff _).mpr (isMultiHomogIdeal_map_coeff _ hP.2.1.2.1)
  have hWh : ∀ W ∈ S, NumbersDVR.IsMultiHomogIdeal W := fun W hW =>
    FieldNumbers.PFContracted.isMultiHomogIdeal_of_mem_minimalPrimes hJ₀h (hS W hW)
  have hWdim : ∀ W ∈ S, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := fun W hW => pcEquidim K ι P e hP W (hS W hW)
  have hmin := mem_minimalPrimes_iInf_iff hS
  have hJh : NumbersDVR.IsMultiHomogIdeal (⨅ W ∈ S, W) := by
    intro f hf b
    simp only [Submodule.mem_iInf] at hf ⊢
    exact fun W hW => hWh W hW f (hf W hW) b
  have hrad := isRadical_iInf (fun W hW => (hS W hW).1.1)
  have hdim : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (⨅ W ∈ S, W)) <
      ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine lt_of_le_of_lt (Inter.BaseChange.ringKrullDim_quotient_le_of_minimalPrimes _
      (N := ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) fun Z hZ => (hWdim Z ((hmin Z).mp hZ)).le) ?_
    exact_mod_cast (show e + Fintype.card K < e + 1 + Fintype.card K by omega)
  rw [NumbersDVR.IntNumAssoc.full ℂ K ι e _ hJh hdim a]
  unfold NumbersDVR.cycEval
  rw [← finsum_mem_coe_finset, finsum_mem_def]
  refine finsum_congr fun W => ?_
  unfold NumbersDVR.idealCycle
  by_cases hW : W ∈ S
  · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hW)]
    have : W.IsPrime := (hS W hW).1.1
    by_cases hrel : NumbersDVR.IsRelevant W
    · rw [dif_pos ⟨(hmin W).mpr hW, hrel⟩, multAt_toNat_of_isRadical hrad ((hmin W).mpr hW)]
      simp
    · rw [dif_neg (fun h => hrel h.2), zero_mul,
        NumbersDVR.IntNumVanish.full ℂ K ι e W this (hWh W hW) (Or.inl hrel) a]
  · rw [Set.indicator_of_notMem (by simpa using hW), dif_neg (fun h => hW ((hmin W).mp h.1)), zero_mul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
