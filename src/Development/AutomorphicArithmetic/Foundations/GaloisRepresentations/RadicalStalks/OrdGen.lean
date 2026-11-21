import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Point
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.NotLeSpanImage
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangianStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCrystalActionAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirectionStatement

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.ParL

variable {C : Type} [CommRing C] [IsDedekindDomain C]

private lemma cop {w J : Ideal C} (hw : w.IsMaximal) (h : ¬ w ∣ J) : IsCoprime w J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  apply h
  rw [Ideal.dvd_iff_le]
  have hle : w ≤ w ⊔ J := le_sup_left
  have heq : w = w ⊔ J := hw.eq_of_le hne hle
  rw [heq]
  exact le_sup_right

private lemma notMem {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a y : C}
    (ha : Ideal.span {a} = w * B) (hB : ¬ w ∣ B) (hy : y ∉ w) (m : ℕ)
    (h : y * a ^ m ∈ w ^ (m + 1)) : False := by
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have h1 : w ^ (m + 1) ∣ Ideal.span {y * a ^ m} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ha, mul_pow,
    pow_succ, show Ideal.span {y} * (w ^ m * B ^ m) = w ^ m * (Ideal.span {y} * B ^ m) by ring] at h1
  have hw0' : w ^ m ≠ 0 := pow_ne_zero _ hw0
  rw [mul_dvd_mul_iff_left hw0'] at h1
  rcases hwp.dvd_or_dvd h1 with h2 | h2
  · apply hy
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  · exact hB (hwp.dvd_of_dvd_pow h2)

private lemma approx {w B : Ideal C} {a : C} (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m k : ℕ) {x : C} (hx : x ∈ w ^ m) : ∃ u, x - a ^ m * u ∈ w ^ (m + k) := by
  have hc' : IsCoprime (B ^ m) (w ^ k) := (hc.symm.pow_left).pow_right
  have htop : B ^ m ⊔ w ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hc'
  have hx' : x ∈ Ideal.span {a} ^ m ⊔ w ^ (m + k) := by
    rw [ha, mul_pow, pow_add, ← Ideal.mul_sup, htop, Ideal.mul_top]
    exact hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, rfl⟩ := hy
  refine ⟨u, ?_⟩
  have : x - a ^ m * u = z := by rw [← hyz]; ring
  rw [this]
  exact hz

private lemma divA {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a : C}
    (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m : ℕ) {x : C} (hx : a * x ∈ w ^ (m + 1)) : x ∈ w ^ m := by
  have h1 : w ^ (m + 1) ∣ Ideal.span {a * x} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hx
  rw [← Ideal.span_singleton_mul_span_singleton, ha, pow_succ', _root_.mul_assoc,
    mul_dvd_mul_iff_left hw0] at h1
  have h2 : w ^ m ∣ Ideal.span {x} := (hc.pow_left).dvd_of_dvd_mul_left h1
  rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2

set_option maxHeartbeats 200000 in

private lemma exPar (p : ℕ) (hp0 : (p : C) ≠ 0) {w : Ideal C} (hw : w.IsMaximal)
    (hpw : (p : C) ∈ w) (f : ℕ) (hf : 0 < f) : Nonempty (Par p w f) := by
  have hw0 : w ≠ ⊥ := by
    intro h0
    apply hp0
    rw [h0] at hpw
    exact (Submodule.mem_bot C).mp hpw
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have hP0 : Ideal.span {(p : C)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  obtain ⟨m, B, hwB, hPB⟩ := WfDvdMonoid.max_power_factor' hP0 hwp.not_unit
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · exfalso
      apply hwB
      rw [pow_zero, _root_.one_mul] at hPB
      rw [← hPB, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hpw
    · exact ⟨n, rfl⟩
  have hcB : IsCoprime w B := cop hw hwB
  have hmemP : ∀ z, z ∈ w ^ (n + 1) → z ∈ B → (p : C) ∣ z := by
    intro z hz1 hz2
    rw [← Ideal.mem_span_singleton, hPB,
      Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp hcB.pow_left)]
    exact Ideal.mem_inf.mpr ⟨hz1, hz2⟩
  have hPle : ∀ z, (p : C) ∣ z → z ∈ w ^ (n + 1) := by
    intro z hz
    have hz' : z ∈ w ^ (n + 1) * B := by
      rw [← hPB]
      exact Ideal.mem_span_singleton.mpr hz
    have hle : w ^ (n + 1) * B ≤ w ^ (n + 1) := Ideal.mul_le_left
    exact hle hz'
  have hcM : IsCoprime (w ^ ((n + 1) * f)) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ ((n + 1) * f) ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcM]
      exact Submodule.mem_top)
  have hεB : j ∈ B := Ideal.pow_le_self hf.ne' hj
  have hi' : i ∈ w ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right _ hf) hi
  have h1ε : 1 - j = i := by
    rw [← hij]
    ring
  have hj1 : j - 1 ∈ w ^ (n + 1) := by
    have e : j - 1 = -i := by
      rw [← h1ε]
      ring
    rw [e]
    exact neg_mem hi'
  have hεw : j - 1 ∈ w := Ideal.pow_le_self (Nat.succ_ne_zero n) hj1
  have hεnot : j ∉ w := by
    intro h
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : j - (j - 1) ∈ w := w.sub_mem h hεw
    rwa [sub_sub_cancel] at h2
  have hnle : ¬ w ≤ w ^ 2 := by
    intro hle
    have h1 : w * w ∣ w * 1 := by
      rw [_root_.mul_one, ← pow_two]
      exact Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_left hw0] at h1
    have h2 := Ideal.dvd_iff_le.mp h1
    rw [Ideal.one_eq_top, top_le_iff] at h2
    exact hw.ne_top h2
  obtain ⟨t, ht, ht2⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc2 : IsCoprime (w ^ 2) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i2, hi2, j2, hj2, hij2⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ 2 ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hc2]
      exact Submodule.mem_top)
  obtain ⟨a, haw, haB, ha2⟩ : ∃ a, a ∈ w ∧ a ∈ B ^ f ∧ a ∉ w ^ 2 := by
    refine ⟨t * j2, w.mul_mem_right _ ht, Ideal.mul_mem_left _ _ hj2, ?_⟩
    intro h
    apply ht2
    have e : t = t * j2 + t * i2 := by
      rw [← mul_add, add_comm, hij2, _root_.mul_one]
    rw [e]
    exact (w ^ 2).add_mem h (Ideal.mul_mem_left _ _ hi2)
  have haBB : a ∈ B := Ideal.pow_le_self hf.ne' haB
  obtain ⟨B', hB'⟩ : w ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haw)
  have hwB' : ¬ w ∣ B' := by
    intro hd
    apply ha2
    have h2 : w ^ 2 ∣ Ideal.span {a} := by
      rw [hB', pow_two]
      exact mul_dvd_mul_left w hd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  have hcB' : IsCoprime w B' := cop hw hwB'
  have hs : (p : C) ^ f ∣ a * (1 - j) := by
    have h3 : (1 - j) * a ∈ w ^ ((n + 1) * f) * B ^ f := by
      refine Ideal.mul_mem_mul ?_ haB
      rw [h1ε]
      exact hi
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hPB, mul_pow, ← pow_mul,
      _root_.mul_comm a]
    exact h3
  obtain ⟨s, hs'⟩ := hs
  have hprod : (p : C) ∣ a * (j * a ^ n) := by
    apply hmemP
    · have e : a * (j * a ^ n) = j * a ^ (n + 1) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haw _)
    · exact Ideal.mul_mem_right _ _ haBB
  obtain ⟨c, hc⟩ := hprod
  have hcw : c ∉ w := by
    intro hcw
    apply notMem hw hw0 hB' hwB' hεnot (n + 1)
    have e : j * a ^ (n + 1) = (p : C) * c := by
      rw [← hc]
      ring
    rw [e, pow_succ]
    exact Ideal.mul_mem_mul (hPle _ dvd_rfl) hcw
  have hcc : IsCoprime (w ^ (n + 1)) (Ideal.span {c}) := by
    refine IsCoprime.pow_left (cop hw ?_)
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  obtain ⟨i3, hi3, j3, hj3, hij3⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ (n + 1) ⊔ Ideal.span {c} by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcc]
      exact Submodule.mem_top)
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hj3
  have hinv : (p : C) ∣ c' * c * j - j := by
    have e1 : c' * c = 1 - i3 := by
      rw [← hij3]
      ring
    have e : c' * c * j - j = -(i3 * j) := by
      rw [e1]
      ring
    rw [e]
    exact hmemP _ (neg_mem (Ideal.mul_mem_right _ _ hi3)) (neg_mem (Ideal.mul_mem_left _ _ hεB))
  have hidem : (p : C) ∣ j * j - j := by
    have e : j * j - j = (j - 1) * j := by ring
    rw [e]
    exact hmemP _ (Ideal.mul_mem_right _ _ hj1) (Ideal.mul_mem_left _ _ hεB)
  have hoff : ∀ (w' : Ideal C), w'.IsMaximal → (p : C) ∈ w' → w' ≠ w → j ∈ w' := by
    intro w' hw' hpw' hne
    have hle : w ^ (n + 1) * B ≤ w' := by
      rw [← hPB]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hpw'
    rcases hw'.isPrime.mul_le.mp hle with h | h
    · exact absurd (hw.eq_of_le hw'.ne_top (hw'.isPrime.le_of_pow_le h)).symm hne
    · exact h hεB
  have hgeps : (p : C) ∣ j * (j * a ^ n) - j * a ^ n := by
    have e : j * (j * a ^ n) - j * a ^ n = (j * j - j) * a ^ n := by ring
    rw [e]
    exact dvd_mul_of_dvd_left hidem _
  have hnil : ∃ e, (p : C) ∣ a ^ e * j :=
    ⟨n + 1, hmemP _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow haw _))
      (Ideal.mul_mem_left _ _ hεB)⟩
  have hgen : ∀ x ∈ w, ∃ u, (p : C) ∣ j * x - a * u := by
    intro x hx
    obtain ⟨u, hu⟩ := approx hB' hcB' 1 n (by rwa [pow_one])
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - a * u = (j - 1) * x + (x - a ^ 1 * u) := by ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hj1) ?_
      rwa [add_comm 1 n] at hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB) (Ideal.mul_mem_right _ _ haBB)
  have hannA : ∀ (x : C), (p : C) ∣ a * x → ∃ u, (p : C) ∣ j * x - j * a ^ n * u := by
    intro x hx
    have hx2 : x ∈ w ^ n := divA hw hw0 hB' hcB' n (hPle _ hx)
    obtain ⟨u, hu⟩ := approx hB' hcB' n 1 hx2
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - j * a ^ n * u = j * (x - a ^ n * u) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hεB))
  have hannG : ∀ (x : C), (p : C) ∣ j * a ^ n * x →
      ∃ u v, (p : C) ∣ x - a * u - (1 - j) * v := by
    intro x hx
    have hxw : x ∈ w := by
      by_contra hxw
      have hy : j * x ∉ w := fun h => (hw.isPrime.mem_or_mem h).elim hεnot hxw
      apply notMem hw hw0 hB' hwB' hy n
      have e : j * x * a ^ n = j * a ^ n * x := by ring
      rw [e]
      exact hPle _ hx
    obtain ⟨u, hu⟩ := hgen x hxw
    refine ⟨u, x, ?_⟩
    have e : x - a * u - (1 - j) * x = j * x - a * u := by ring
    rw [e]
    exact hu
  exact ⟨Par.mk j a (j * a ^ n) c c' s hidem hεw hoff haw hs' hc hinv hgeps hnil hgen
    hannG hannA⟩

end UpperTheory.Gal.Ord.ParL

theorem UpperTheory.Gal.Ord.par :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (w : Ideal (𝓞 F)) (f : ℕ), w.IsMaximal → (p : 𝓞 F) ∈ w → 0 < f → Nonempty (Par p w f) := by
  intro p _ F _ _ w f hw hpw hf
  exact UpperTheory.Gal.Ord.ParL.exPar p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hw hpw f hf
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem laurent_adjoin_eq_of_image_eq {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (h0 : 0 < Module.finrank ℤ O) :
    Function.Injective (algebraMap (𝓞 F) O) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hI : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hmem : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : 𝓞 F) ∈ Ideal.span {x} := Ideal.absNorm_mem _
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  have hn0 : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have h1 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : O) = 0 := by
    rw [← map_natCast (algebraMap (𝓞 F) O), ← hy, map_mul, hx, mul_zero]
  have h2 : ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (1 : O) =
      ((Ideal.absNorm (Ideal.span {x}) : ℕ) : ℤ) • (0 : O) := by
    rw [smul_zero, zsmul_eq_mul, _root_.mul_one]
    exact_mod_cast h1
  have h3 : (1 : O) = 0 := smul_right_injective O (by exact_mod_cast hn0) h2
  haveI : Subsingleton O := subsingleton_of_zero_eq_one h3.symm
  rw [Module.finrank_zero_of_subsingleton] at h0
  exact lt_irrefl 0 h0

private theorem wachExpansion_smul_compatible {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F)
    (hinj : Function.Injective (algebraMap (𝓞 F) O)) (x : O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c := by
  classical
  let b := Module.finBasis ℤ (𝓞 F)
  let v : Option (Fin (Module.finrank ℤ (𝓞 F))) → O :=
    fun o => Option.elim o x (fun i => algebraMap (𝓞 F) O (b i))
  have hcard : ¬ LinearIndependent ℤ v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, hr, RingOfIntegers.rank] at hle
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hcard
  rw [Fintype.sum_option] at hg
  have hmap : algebraMap (𝓞 F) O (∑ j, g (some j) • b j) =
      ∑ j, g (some j) • algebraMap (𝓞 F) O (b j) := by
    rw [map_sum]
    simp only [map_zsmul]
  have hg' : g none • x + algebraMap (𝓞 F) O (∑ j, g (some j) • b j) = 0 := by
    rw [hmap]
    simpa [v] using hg
  have hnone : g none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg'
    have hc0 : ∑ j, g (some j) • b j = 0 := hinj (by rw [hg', map_zero])
    have hall := (Fintype.linearIndependent_iff.mp b.linearIndependent) (fun j => g (some j)) hc0
    cases i with
    | none => exact hi h0
    | some j => exact hi (hall j)
  refine ⟨g none, hnone, -(∑ j, g (some j) • b j), ?_⟩
  rw [map_neg, eq_neg_iff_add_eq_zero]
  exact hg'

private theorem surj_comm {F O : Type} [Field F] [NumberField F] [CommRing O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O]
    (hinj : Function.Injective (algebraMap (𝓞 F) O))
    (hs : ∀ x : O, ∃ e : ℤ, e ≠ 0 ∧ ∃ c : 𝓞 F, e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  classical
  intro x
  obtain ⟨e, he, c, hc⟩ := hs x
  obtain ⟨P, hPm, hPx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have hQ : Polynomial.aeval (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hc, algebraMap_int_eq, Int.coe_castRingHom, zsmul_eq_mul]
  rw [hex, Polynomial.aeval_algebraMap_apply] at hQ
  have hQ' : Polynomial.aeval c (P.scaleRoots e) = 0 := hinj (by rw [hQ, map_zero])
  have hQF : Polynomial.aeval (c : F) (P.scaleRoots e) = 0 := by
    have h0 := congrArg (algebraMap (𝓞 F) F) hQ'
    rwa [map_zero, ← Polynomial.aeval_algebraMap_apply] at h0
  have he' : ((e : ℤ) : F) ≠ 0 := by exact_mod_cast he
  have hmul : algebraMap ℤ F e * ((c : F) / e) = (c : F) := by
    rw [eq_intCast]
    field_simp
  have hz : Polynomial.eval₂ (algebraMap ℤ F) ((c : F) / e) P = 0 := by
    have h := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ F) ((c : F) / e) e
    rw [hmul, ← Polynomial.aeval_def, hQF] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by rwa [eq_intCast]))
  let d : 𝓞 F := ⟨(c : F) / e, ⟨P, hPm, hz⟩⟩
  have hed : (e : 𝓞 F) * d = c := by
    apply RingOfIntegers.ext
    show ((e : 𝓞 F) : F) * ((c : F) / e) = (c : F)
    have hcoe : ((e : 𝓞 F) : F) = (e : F) := by
      first
        | simp
        | exact map_intCast (algebraMap (𝓞 F) F) e
    rw [hcoe]
    field_simp
  refine ⟨d, ?_⟩
  apply smul_right_injective O he
  show e • algebraMap (𝓞 F) O d = e • x
  rw [hc, ← hed, map_mul, map_intCast, zsmul_eq_mul]

private theorem exists_finset_adjoin_laurent_preimage {F O : Type} [Field F] [NumberField F] [Ring O] [Algebra (𝓞 F) O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hr : Module.finrank ℤ O = Module.finrank ℚ F) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  have hpos : 0 < Module.finrank ℤ O := by
    rw [hr]
    exact Module.finrank_pos
  have hinj := laurent_adjoin_eq_of_image_eq (F := F) (O := O) hpos
  have hs := wachExpansion_smul_compatible (F := F) (O := O) hr hinj
  have hcomm : ∀ x y : O, x * y = y * x := by
    intro x y
    obtain ⟨a, ha, c, hc⟩ := hs x
    obtain ⟨b, hb, c', hc'⟩ := hs y
    apply smul_right_injective O (mul_ne_zero ha hb)
    show (a * b) • (x * y) = (a * b) • (y * x)
    calc (a * b) • (x * y) = (a • x) * (b • y) := by rw [smul_mul_smul_comm]
      _ = algebraMap (𝓞 F) O (c * c') := by rw [hc, hc', map_mul]
      _ = algebraMap (𝓞 F) O (c' * c) := by rw [_root_.mul_comm c c']
      _ = (b • y) * (a • x) := by rw [hc, hc', map_mul]
      _ = (a * b) • (y * x) := by rw [smul_mul_smul_comm, _root_.mul_comm b a]
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  exact surj_comm hinj hs

theorem UpperTheory.Gal.Ord.surjO :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  apply exists_finset_adjoin_laurent_preimage
  rw [D.rankO, hm]
  simp
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem exists_rep {k H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    (φ : LinearMap.BilinForm k H) (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (L : H →ₗ[k] k) : ∃ α, ∀ h, φ h α = L h := by
  have hinj : Function.Injective φ.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd
    intro h
    have this : φ h y = 0 := LinearMap.congr_fun hy h
    rw [hskew, this, neg_zero]
  have hsurj : Function.Surjective φ.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨α, hα⟩ := hsurj L
  exact ⟨α, fun h => by rw [← hα]; rfl⟩

private theorem ks_core {k H C : Type*} [Field k] [AddCommGroup H] [Module k H] [CommRing C]
    (σ : C →+* Module.End k H) (bar : C → C) (χ : C →+* k) (φ : LinearMap.BilinForm k H) (Fl : Submodule k H)
    (hskew : ∀ x y, φ x y = -φ y x) (hnd : ∀ x, (∀ y, φ x y = 0) → x = 0)
    (hiso : ∀ x ∈ Fl, ∀ y ∈ Fl, φ x y = 0)
    (hadj : ∀ c x y, φ (σ c x) y = φ x (σ (bar c) y))
    (ω e : C) (T r : k) (hT : ∀ v, σ ω v + σ (bar ω) v = T • v) (hdisc : 2 * r - T ≠ 0)
    (hL1 : ∀ c h, σ c (σ e h) - χ c • σ e h ∈ Fl) (hL3 : ∀ h, σ ω (σ e h) = r • σ e h)
    (h₀ : H) (hh₀ : σ e h₀ ∉ Fl) (x : H) (hxe : σ e x = x) (α : H)
    (hα : ∀ c h, φ (σ c h) α = χ c * φ h α) (hxα : φ x α ≠ 0) :
    ∃ g : H →ₗ[k] H,
      (∀ c, ∀ u ∈ Fl, g (σ c u) - σ c (g u) ∈ Fl) ∧
      (∀ (n : ℕ) (lam : Fin n → k) (c : Fin n → C) (u : H), ∑ l, lam l * χ (c l) = 0 →
        g (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) = 0) ∧
      (∀ u ∈ Fl, ∀ v ∈ Fl, φ (g u) v + φ u (g v) = 0) ∧ g x ∉ Fl := by
  have hcomm : ∀ a b v, σ a (σ b v) = σ b (σ a v) := by
    intro a b v
    show (σ a * σ b) v = (σ b * σ a) v
    rw [← map_mul, ← map_mul, mul_comm]
  have hbar : ∀ v, σ (bar ω) v = T • v - σ ω v := by
    intro v
    rw [← hT v]
    abel
  have hzw : ∀ c, σ ω (σ c (σ e h₀)) = r • σ c (σ e h₀) := by
    intro c
    rw [hcomm, hL3 h₀, map_smul]
  have hαc : ∀ c, σ c α = χ (bar c) • α := by
    intro c
    rw [← sub_eq_zero]
    apply hnd
    intro y
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hadj c α y,
      hskew α (σ (bar c) y), hα (bar c) y, hskew α y]
    ring
  have hwfl : ∀ c, ∀ u ∈ Fl, φ u (σ (bar c) (σ e h₀)) = χ (bar c) * φ u (σ e h₀) := by
    intro c u hu
    have h1 := hiso u hu _ (hL1 (bar c) h₀)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    exact h1
  have hxw : φ x (σ e h₀) = 0 := by
    have h1 : φ (σ ω x) (σ e h₀) = r * φ x (σ e h₀) := by
      rw [← hxe, hL3 x, hxe, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h2 : φ (σ ω x) (σ e h₀) = (T - r) * φ x (σ e h₀) := by
      rw [hadj, hbar, hL3 h₀, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    have h3 : (2 * r - T) * φ x (σ e h₀) = 0 := by
      linear_combination h2 - h1
    exact (mul_eq_zero.1 h3).resolve_left hdisc
  have hPz : ∀ d v, φ ((σ ω - (T - r) • 1) v) (σ d (σ e h₀)) = 0 := by
    intro d v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      smul_eq_mul]
    rw [hadj, hbar, hzw, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have happ : ∀ u, ((φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α) u =
      φ u α • σ e h₀ + φ u (σ e h₀) • α := fun u => rfl
  refine ⟨(φ.flip α).smulRight (σ e h₀) + (φ.flip (σ e h₀)).smulRight α, ?_, ?_, ?_, ?_⟩
  · intro c u hu
    rw [happ, happ, map_add, map_smul, map_smul, hα c u, hadj c u (σ e h₀), hwfl c u hu, hαc c]
    have key : (χ c * φ u α) • σ e h₀ + (χ (bar c) * φ u (σ e h₀)) • α -
        (φ u α • σ c (σ e h₀) + φ u (σ e h₀) • χ (bar c) • α) =
        -(φ u α • (σ c (σ e h₀) - χ c • σ e h₀)) := by
      module
    rw [key]
    exact Fl.neg_mem (Fl.smul_mem _ (hL1 c h₀))
  · intro n lam c u hsum
    rw [happ]
    have h1 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) α = 0 := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hα]
      have e1 : ∀ l, lam l * (χ (c l) * φ ((σ ω - (T - r) • 1) u) α) =
          (lam l * χ (c l)) * φ ((σ ω - (T - r) • 1) u) α := fun l => by ring
      rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.sum_mul, hsum, zero_mul]
    have h2 : φ (∑ l, lam l • σ (c l) ((σ ω - (T - r) • 1) u)) (σ e h₀) = 0 := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hadj, hPz,
        mul_zero, Finset.sum_const_zero]
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  · intro u _ v _
    rw [happ, happ, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hskew (σ e h₀) v, hskew α v]
    ring
  · rw [happ, hxw, zero_smul, add_zero]
    intro hmem
    apply hh₀
    have := Fl.smul_mem (φ x α)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hxα, one_smul] at this

theorem UpperTheory.Gal.Ord.ks :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ φ : LinearMap.BilinForm k (HdR o.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o.A o.A o.P φ → ∀ x ∈ Fil o.A, hom o π.ε x = x →
      (∃ y, (∀ c, coh o c y = β (b.t i c) • y) ∧ x y ≠ 0) →
      ∃ g : HdR o.A →ₗ[k] HdR o.A, GlobalTheory.UPel.Sm.IsKS (GlobalTheory.HTCount.crysAct o) φ (Fil o.A) (GlobalTheory.HTCount.lieZ o β) g ∧ g x ∉ Fil o.A := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hf hf0 π φ hφ x hxF hxe hyex
  obtain ⟨y, hy, hxy⟩ := hyex
  obtain ⟨hfd, -, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k (spMap β) o β rfl φ hφ
  have hadj0 := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k (spMap β) o β rfl φ hφ
  obtain ⟨hL1, ⟨h₀, hh₀, -⟩, hL3⟩ := lie p D R b N hN hNp hm k hk β o i w f hw hf hf0 π
  haveI := hfd
  let L : HdR o.A →ₗ[k] k :=
    { toFun := fun h => h y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨α, hα0⟩ := exists_rep φ hskew hnd L
  let σ : 𝓞 D.F →+* Module.End k (HdR o.A) := (GlobalTheory.HTCount.crysAct o).comp (algebraMap (𝓞 D.F) D.O)
  have hadj : ∀ c u v, φ (σ c u) v = φ u (σ (D.bar c) v) := by
    intro c u v
    have := hadj0 (algebraMap _ _ c) u v
    rwa [D.star_F, MulOpposite.unop_op] at this
  have hT : ∀ v, σ D.ω v + σ (D.bar D.ω) v = (D.tr : k) • v := by
    intro v
    have e1 : σ D.ω + σ (D.bar D.ω) = σ (D.tr : 𝓞 D.F) := by
      rw [← map_add, D.tr_eq]
    have e2 := LinearMap.congr_fun e1 v
    rw [LinearMap.add_apply, map_intCast] at e2
    rw [e2]
    simp only [Module.End.intCast_apply]
    exact (Int.cast_smul_eq_zsmul k D.tr v).symm
  have hdisc : 2 * β b.ρ - (D.tr : k) ≠ 0 := by
    haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 hk
    intro h0
    have hr := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_pow, map_mul, map_intCast, map_zero] at hr
    have e3 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * β b.ρ - D.tr) * h0 - 4 * hr
    exact D.disc_p ((CharP.intCast_eq_zero_iff k p _).1 e3)
  have hα : ∀ c h, φ (σ c h) α = (β.comp (b.t i)) c * φ h α := by
    intro c h
    rw [hα0, hα0]
    show h (coh o c y) = _
    rw [hy c, map_smul, smul_eq_mul]
    rfl
  have hxα : φ x α ≠ 0 := by
    rw [hα0]
    exact hxy
  obtain ⟨g, ga, gb, gc, gd⟩ := ks_core σ D.bar (β.comp (b.t i)) φ (Fil o.A) hskew hnd hiso hadj D.ω π.ε
    (D.tr : k) (β b.ρ) hT hdisc hL1 hL3 h₀ hh₀ x hxe α hα hxα
  refine ⟨g, ⟨?_, ?_, gc⟩, gd⟩
  · intro a u hu
    obtain ⟨c, rfl⟩ := surjO p D hm a
    exact ga c u hu
  · intro z hz
    have hle : GlobalTheory.HTCount.lieZ o β ≤ (Fil o.A).comap g := by
      apply Submodule.span_le.2
      rintro z ⟨n, lam, c, y', hy', hsum, rfl⟩
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy'
      exact (congrArg (· ∈ Fil o.A) (gb n lam c u (hsum i))).mpr (Fil o.A).zero_mem
    exact hle hz
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section SlopeTestRemainingChoices

open GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {A : Over (Sp R)} [GrpObj A]
  {A' : Over (Sp R')} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem pull_primPull (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (e : A ⟶ A) (e' : A' ⟶ A')
    [IsMonHom e] [IsMonHom e'] (he : e'.left ≫ φ = φ ≫ e.left) (c : primDR A) :
    (bcMor h).pull (primPull (dp0 R) (𝟙 _) e c) = primPull (dp0 R') (𝟙 _) e' ((bcMor h).pull c) := by
  have e1 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) e) (bcMor h)
    (GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) rfl c
  have e2 := GrpMor.pull_pull (bcMor h) (homMor (dp0 R') (𝟙 _) e')
    (GrpMor.comp (homMor (dp0 R) (𝟙 _) e) (bcMor h)) (fun _ => rfl) he c
  exact e1.trans e2.symm

private theorem pull_frob_iter (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (f : ℕ) (c : primDR A) :
    (bcMor h).pull ((frobDR p R hR A)^[f] c) = (frobDR p R' hR' A')^[f] ((bcMor h).pull c) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', GlobalTheory.LinFrob.pull_frobDR p hR hR' h, ih]

private theorem frob_iter_smul (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (f : ℕ) (r : R) (c : primDR A) :
    (frobDR p R hR A)^[f] (r • c) = r ^ p ^ f • (frobDR p R hR A)^[f] c := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, GlobalTheory.LinFrob.frobDR_smul p hR, pow_succ,
      pow_mul]

private theorem pull_mem_span (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (g : A ⟶ A) (g' : A' ⟶ A') [IsMonHom g] [IsMonHom g']
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) {y : primDR A}
    (hy : y ∈ Submodule.span R (Set.range fun c => primPull (dp0 R) (𝟙 _) g ((frobDR p R hR A)^[f] c))) :
    (bcMor h).pull y ∈
      Submodule.span R' (Set.range fun c => primPull (dp0 R') (𝟙 _) g' ((frobDR p R' hR' A')^[f] c)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    refine Submodule.subset_span ⟨(bcMor h).pull c, ?_⟩
    simp only
    rw [pull_primPull h g g' hg, pull_frob_iter p hR hR' h]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ ha

private theorem no_up (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0) (hR' : (p : R') = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p R hR A e g f) : NO p R' hR' A' e' g' f := by
  intro x hx
  rw [(GlobalTheory.abelianDeRham.2.2.1 R A d hA hd R' A' φ h).2] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    rw [← pull_primPull h e e' he]
    exact pull_mem_span p hR hR' h g g' hg f (hN c hc)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

end SlopeTestRemainingChoices

section Down

open GlobalTheory.Published.AbelianDeRham

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Over (Sp K)} [GrpObj A]
  {A' : Over (Sp L)} [GrpObj A'] {φ : A'.left ⟶ A.left}

private theorem mem_of_subtype_baseChange_eq_one_tmul {K L : Type} {V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (y : V) (s : L ⊗[K] W) (hs : (W.subtype.baseChange L) s = (1 : L) ⊗ₜ[K] y) : y ∈ W := by
  have hcomp : W.mkQ ∘ₗ W.subtype = 0 := by
    ext w
    exact (Submodule.Quotient.mk_eq_zero W).mpr w.2
  have hq : (W.mkQ.baseChange L) ((W.subtype.baseChange L) s) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hcomp, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [hs, LinearMap.baseChange_tmul] at hq
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (TensorProduct.lid K (V ⧸ W)) (LinearMap.rTensor (V ⧸ W) g ((1 : L) ⊗ₜ[K] W.mkQ y)) = 0 := by
    rw [hq, map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hg1, one_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h2
  exact h2

set_option maxHeartbeats 200000 in

private theorem no_down (p : ℕ) [Fact p.Prime] (hK : (p : K) = 0) (hL : (p : L) = 0)
    (h : IsGrpPullback A' A (spMap (algebraMap K L)) φ) (d : ℕ) (hA : IsAbelianScheme A)
    (hd : SmoothOfRelativeDimension d A.hom) (e g : A ⟶ A) (e' g' : A' ⟶ A')
    [IsMonHom e] [IsMonHom g] [IsMonHom e'] [IsMonHom g'] (he : e'.left ≫ φ = φ ≫ e.left)
    (hg : g'.left ≫ φ = φ ≫ g.left) (f : ℕ) (hN : NO p L hL A' e' g' f) : NO p K hK A e g f := by
  obtain ⟨-, -, hBC, -, -⟩ := GlobalTheory.abelianDeRham
  obtain ⟨hbij, hF⟩ := hBC K A d hA hd L A' φ h
  unfold NO at hN ⊢
  intro x hx
  have hPx : (bcMor h).pull x ∈ PrimitiveSubmodule A' := by
    rw [hF]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hy' := hN _ hPx
  rw [← pull_primPull h e e' he] at hy'
  obtain ⟨W, hW⟩ : ∃ W, W = Submodule.span K
      (Set.range fun c => primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] c)) := ⟨_, rfl⟩
  rw [← hW]
  let Φ : L ⊗[K] W →ₗ[L] primDR A' := (liftSemi (bcMor h).pull).comp (W.subtype.baseChange L)
  have hΦ : ∀ (a : L) (w : W), Φ (a ⊗ₜ[K] w) = a • (bcMor h).pull (w : primDR A) := by
    intro a w
    simp only [Φ, LinearMap.comp_apply, LinearMap.baseChange_tmul, liftSemi_tmul, Submodule.subtype_apply]
  have hgen : ∀ t : L ⊗[K] primDR A,
      primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] (liftSemi (bcMor h).pull t)) ∈ LinearMap.range Φ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, iterate_map_zero, map_zero]
      exact Submodule.zero_mem _
    | tmul a v =>
      rw [liftSemi_tmul, frob_iter_smul p hL f a, ← pull_frob_iter p hK hL h f v, map_smul,
        ← pull_primPull h g g' hg]
      have hmem : primPull (dp0 K) (𝟙 (Sp K)) g ((frobDR p K hK A)^[f] v) ∈ W := by
        rw [hW]
        exact Submodule.subset_span ⟨v, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(a ^ p ^ f) ⊗ₜ[K] (⟨_, hmem⟩ : W), hΦ _ _⟩
    | add t1 t2 h1 h2 =>
      rw [map_add, iterate_map_add, map_add]
      exact Submodule.add_mem _ h1 h2
  have hle : Submodule.span L (Set.range fun c => primPull (dp0 L) (𝟙 (Sp L)) g' ((frobDR p L hL A')^[f] c)) ≤
      LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨t, ht⟩ := hbij.2 c
    have h4 := hgen t
    rw [SetLike.mem_coe, ← ht]
    exact h4
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp (hle hy')
  simp only [Φ, LinearMap.comp_apply] at hs
  have h5 : liftSemi (bcMor h).pull (W.subtype.baseChange L s) =
      liftSemi (bcMor h).pull ((1 : L) ⊗ₜ[K] primPull (dp0 K) (𝟙 (Sp K)) e x) := by
    rw [liftSemi_tmul, one_smul]
    exact hs
  have h6 := hbij.1 h5
  exact mem_of_subtype_baseChange_eq_one_tmul W _ s h6

end Down

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.desc :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ) (π : Par p w f)
      (κ k T : Type) [Field κ] [Field k] [CommRing T] (hκ : (p : κ) = 0) (hk : (p : k) = 0) (hT : (p : T) = 0) (σ : κ →+* k) (τ : κ →+* T)
      (s : Sp κ ⟶ Sp R) (s₀ : Sp k ⟶ Sp R) (s' : Sp T ⟶ Sp R) (o : Obj b N s) (o₀ : Obj b N s₀) (o' : Obj b N s'),
      ObjMap o₀ o (spMap σ) → ObjMap o' o (spMap τ) → NOo hk o₀ π → NOo hT o' π := by
  intro p _ D R _ b N w f π κ k T _ _ _ hκ hk hT σ τ s s₀ s' o o₀ o' m₀ m' hN
  letI : Algebra κ k := σ.toAlgebra
  letI : Algebra κ T := τ.toAlgebra
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o₀.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.ε)
  haveI := o'.act.hom ((algebraMap (𝓞 D.F) D.O) π.g)
  have hd := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle p D R b N _ s o
  have h1 : NOo hκ o π :=
    no_down p hκ hk m₀.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
      (o₀.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m₀.act _) (m₀.act _) f hN
  exact no_up p hκ hT m'.cart D.g o.ab hd.1 (o.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.ε))
    (o'.act.act ((algebraMap (𝓞 D.F) D.O) π.g)) (m'.act _) (m'.act _) f h1
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

section
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]
  {A' : Over (Sp (DualNumber k))} [GrpObj A'] {i : A₀.left ⟶ A'.left}

private theorem resMor (h : IsGrpPullback A₀ A' (epsRed k) i) :
    GrpMor (dp0 (DualNumber k)) (𝟙 _) A' (dp0 k) (𝟙 _) A₀ (TrivSqZeroExt.fstHom k k k).toRingHom (epsRed k) i :=
  GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) (by simp; rfl) h

private theorem frob_sq (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) :
    GlobalTheory.VB.frob A₀.left p (cast_left p k hk A₀) ≫ i = i ≫ GlobalTheory.VB.frob A'.left p (cast_left p _ hT A') :=
  GlobalTheory.VB.frob_naturality p (cast_left p _ hT A') i (cast_left p k hk A₀)

private theorem pow_dual (hk : (p : k) = 0) (r : DualNumber k) :
    r ^ p = algebraMap k (DualNumber k) (TrivSqZeroExt.fst r ^ p) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_pow]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_pow, nsmul_eq_mul, hk]

private theorem res_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (resMor h).pull (frobDR p _ hT A' c) = frobDR p k hk A₀ ((resMor h).pull c) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (resMor h)
  refine (GrpMor.pull_pull F' (resMor h) M (fun _ ↦ rfl) rfl c).trans
    (GrpMor.pull_pull (resMor h) F₀ M (fun r ↦ ?_) (frob_sq hk hT) c).symm
  simp [frobR_apply, TrivSqZeroExt.fst_pow]

private theorem lift_frob (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (c : primDR A') :
    (liftMor (epsDP k) h).pull (frobDR p _ hT A' c) =
      (constMor A₀).pull (frobDR p k hk A₀ ((resMor h).pull c)) := by
  have F' := frobMor p _ hT A' (cast_left p _ hT A')
  have F₀ := frobMor p k hk A₀ (cast_left p k hk A₀)
  have M := F'.comp (liftMor (epsDP k) h)
  have N := (resMor h).comp F₀
  have e₁ := GrpMor.pull_pull F' (liftMor (epsDP k) h) M (fun _ ↦ rfl) rfl c
  have e₂ := GrpMor.pull_pull (resMor h) F₀ N (fun _ ↦ rfl) rfl c
  have e₃ := GrpMor.pull_pull N (constMor A₀) M (fun r ↦ by
    simp [frobR_apply, pow_dual hk r]) (by simpa using frob_sq hk hT) c
  exact e₁.trans (e₃.symm.trans (congrArg _ e₂.symm))

private theorem res_iter (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (n : ℕ) (c : primDR A') :
    (resMor h).pull ((frobDR p _ hT A')^[n] c) = (frobDR p k hk A₀)^[n] ((resMor h).pull c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', res_frob hk hT h, ih]

private theorem corr_push {x : HdR A₀} {d : Crys (epsDP k) (epsRed k) A₀}
    (hd : (constMor A₀).Corr x d) (u : A₀ ⟶ A₀) [IsMonHom u] (c : primDR A₀) :
    push (epsDP k) (epsRed k) u d ((constMor A₀).pull c) =
      algebraMap k (DualNumber k) (push (dp0 k) (𝟙 _) u x c) :=
  GrpMor.Corr.push (m := constMor A₀) (constMor A₀) u u (by simp) hd c

private theorem vanish (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (g₀ : A₀ ⟶ A₀) (g' : A' ⟶ A') [IsMonHom g₀] [IsMonHom g']
    (hg : i ≫ g'.left = g₀.left ≫ i) (n : ℕ) (x : HdR A₀) (d : Crys (epsDP k) (epsRed k) A₀)
    (hd : (constMor A₀).Corr x d)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[n + 1] z)) = 0) (c : primDR A') :
    crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) = 0 := by
  have e₁ : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p _ hT A')^[n + 1] c)) =
      push (epsDP k) (epsRed k) g₀ d ((liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c)) :=
    (LinearMap.congr_fun (crysToDR_push (epsDP k) h h g₀ g' hg d) _).symm
  have e₂ : (liftMor (epsDP k) h).pull ((frobDR p _ hT A')^[n + 1] c) =
      (constMor A₀).pull ((frobDR p k hk A₀)^[n + 1] ((resMor h).pull c)) := by
    rw [Function.iterate_succ_apply', lift_frob hk hT h, res_iter hk hT h,
      Function.iterate_succ_apply']
  rw [e₁, e₂, corr_push hd g₀, push_apply, hx, map_zero]

private theorem dual_zero_of_span {T M : Type*} [CommRing T] [AddCommGroup M] [Module T M] (L : M →ₗ[T] T)
    {S : Set M} (hS : ∀ s ∈ S, L s = 0) {y : M} (hy : y ∈ Submodule.span T S) : L y = 0 :=
  LinearMap.mem_ker.1 ((Submodule.span_le (p := LinearMap.ker L)).2 (fun s hs ↦ LinearMap.mem_ker.2 (hS s hs)) hy)

private theorem alg_eq (a : k) :
    algebraMap k (DualNumber k) a = TrivSqZeroExt.inl a + TrivSqZeroExt.inr 0 := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 1600000 in
private theorem core (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0)
    (h : IsGrpPullback A₀ A' (epsRed k) i) (hBC : (constMor A₀).IsBC)
    (e₀ g₀ : A₀ ⟶ A₀) (e' g' : A' ⟶ A') [IsMonHom e₀] [IsMonHom g₀] [IsMonHom e'] [IsMonHom g']
    (he : i ≫ e'.left = e₀.left ≫ i) (hg : i ≫ g'.left = g₀.left ≫ i) (f : ℕ) (hf : 0 < f)
    (hNO : NO p (DualNumber k) hT A' e' g' f) (x : HdR A₀)
    (hx : ∀ z, x (primPull (dp0 k) (𝟙 _) g₀ ((frobDR p k hk A₀)^[f] z)) = 0) :
    IsFilLift h (push (dp0 k) (𝟙 _) e₀ x) 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨d, hd⟩ := hBC.exists x
  refine ⟨push (epsDP k) (epsRed k) e₀ d, ?_, fun c ↦ ?_⟩
  · have hpush := crysToDR_push (epsDP k) h h e₀ e' he d
    change crysToDR (epsDP k) h (push (epsDP k) (epsRed k) e₀ d) ∈ Fil A'
    rw [hpush]
    refine (Submodule.mem_dualAnnihilator _).2 fun y hy ↦ ?_
    have hmem : primPull (dp0 (DualNumber k)) (𝟙 _) e' y ∈ Submodule.span (DualNumber k)
        (Set.range fun c => primPull (dp0 (DualNumber k)) (𝟙 _) g' ((frobDR p (DualNumber k) hT A')^[n + 1] c)) :=
      hNO y hy
    have h0 : crysToDR (epsDP k) h d (primPull (dp0 (DualNumber k)) (𝟙 _) e' y) = 0 :=
      dual_zero_of_span _ (Set.forall_mem_range.2 (vanish hk hT h hBC g₀ g' hg n x d hd hx)) hmem
    exact h0
  · have e₁ := corr_push (x := x) (d := d) hd e₀ c
    exact e₁.trans (alg_eq _)

end

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.estep :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (f : ℕ), 0 < f → ∀ (π : Par p w f)
      (k : Type) [Field k] (hk : (p : k) = 0) (hT : (p : DualNumber k) = 0) (s₀ : Sp k ⟶ Sp R) (s' : Sp (DualNumber k) ⟶ Sp R) (o₀ : Obj b N s₀) (o' : Obj b N s')
      (m : ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), NOo hT o' π →
      ∀ x : HdR o₀.A, (∀ z, x (coh o₀ π.g ((frobDR p k hk o₀.A)^[f] z)) = 0) → IsFilLift m.cart (hom o₀ π.ε x) 0 := by
  intro p _ D R _ b N w f hf π k _ hk hT s₀ s' o₀ o' m hNO x hx
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  exact core hk hT m.cart (GlobalTheory.HTRealise.isBC_constMor o₀.ab) _ _ _ _ (m.act _).symm (m.act _).symm f hf hNO x hx
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem radical_quot (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (m : Ideal R) [m.IsMaximal] : (m.map (algebraMap R B)).IsRadical := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : _root_.IsReduced ((R ⧸ m) ⊗[R] B) := GlobalTheory.T.isReduced_of_smooth_over_field' (R ⧸ m) _
  have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  haveI : _root_.IsReduced (B ⧸ m.map (algebraMap R B)) :=
    isReduced_of_injective e.toRingEquiv.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

private theorem radical_loc (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) (hI : I.IsRadical) : (I.map (algebraMap B A)).IsRadical := by
  intro a ⟨n, hn⟩
  have hn' : a ^ (n + 1) ∈ I.map (algebraMap B A) := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hn
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq M a
  obtain ⟨⟨i, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hn'
  have hu : IsLocalization.mk' A b u * algebraMap B A u = algebraMap B A b := IsLocalization.mk'_spec A b u
  have e1 : algebraMap B A (b ^ (n + 1) * t) = algebraMap B A (i * u ^ (n + 1)) := by
    simp only [map_mul, map_pow]
    rw [← ht, ← hu]
    ring
  obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := M) e1
  have hy : (d : B) * t * b ∈ I := by
    apply hI
    refine ⟨n + 1, ?_⟩
    have e2 : ((d : B) * t * b) ^ (n + 1) = ((d : B) * t) ^ n * ((d : B) * (b ^ (n + 1) * t)) := by ring
    rw [e2, hd]
    exact I.mul_mem_left _ (I.mul_mem_left _ (I.mul_mem_right _ i.2))
  refine (IsLocalization.mem_map_algebraMap_iff M A).mpr
    ⟨⟨⟨_, hy⟩, u * d * t⟩, ?_⟩
  simp only [Submonoid.coe_mul, map_mul]
  rw [← hu]
  ring

private theorem radical_stalk (R : Type) [CommRing R] (m : Ideal R) [m.IsMaximal] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X) (r : CommRingCat.of R ⟶ X.presheaf.stalk z)
    (hr : Spec.map r = X.fromSpecStalk z ≫ s) : (m.map r.hom).IsRadical := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hsm : Smooth (hU.fromSpec ≫ s) := inferInstance
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hρs : ρ.hom.Smooth := by
    rw [← hρ] at hsm
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  have e : r = ρ ≫ X.presheaf.germ U z hzU := by
    apply Spec.map_injective
    rw [hr, Spec.map_comp, hρ, ← hU.fromSpecStalk_eq_fromSpecStalk hzU]
    simp [IsAffineOpen.fromSpecStalk]
  letI := ρ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, U) := hρs
  have h1 := radical_quot R Γ(X, U) m
  letI : Algebra Γ(X, U) (X.presheaf.stalk z) := (X.presheaf.germ U z hzU).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hzU⟩
  have h2 := radical_loc Γ(X, U) (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl _ h1
  rw [Ideal.map_map] at h2
  rw [e]
  exact h2

private theorem kills_max (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of R)) [Smooth s] (z : X)
    (hmax : ∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z)
    (T : Type) [CommRing T] (φ : X.presheaf.stalk z ⟶ CommRingCat.of T) (c : R →+* T)
    (h : Spec.map φ ≫ X.fromSpecStalk z ≫ s = Spec.map (CommRingCat.ofHom c))
    (hc : ∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) :
    ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), φ.hom x = 0 := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (X.fromSpecStalk z ≫ s)
  have hrc : r ≫ φ = CommRingCat.ofHom c := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr, h]
  have hrad := radical_stalk R (IsLocalRing.maximalIdeal R) X s z r hr
  have hprime : ∀ P : Ideal (X.presheaf.stalk z), P.IsPrime →
      (IsLocalRing.maximalIdeal R).map r.hom ≤ P → P = IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    intro P hP hJ
    let y : Spec (X.presheaf.stalk z) := ⟨P, hP⟩
    have h1 : X.fromSpecStalk z y ⤳ z := by
      have : X.fromSpecStalk z y ∈ Set.range (X.fromSpecStalk z) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : s.base (X.fromSpecStalk z y) = IsLocalRing.closedPoint R := by
      have e : s.base (X.fromSpecStalk z y) = (Spec.map r).base y := by rw [hr]; rfl
      rw [e]
      apply PrimeSpectrum.ext
      have hle : IsLocalRing.maximalIdeal R ≤ P.comap r.hom := Ideal.map_le_iff_le_comap.mp hJ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap r.hom).ne_top hle).symm
    have h3 := hmax _ h2 h1
    have h4 : y = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      (X.fromSpecStalk z).isEmbedding.injective (h3.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  intro x hx
  have hxJ : x ∈ (IsLocalRing.maximalIdeal R).map r.hom := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Ideal.mem_sInf.mpr fun {P} hP => ?_
    rw [hprime P hP.2 hP.1]
    exact hx
  have hker : (IsLocalRing.maximalIdeal R).map r.hom ≤ RingHom.ker φ.hom := by
    refine Ideal.map_le_iff_le_comap.mpr fun y hy => ?_
    have e : φ.hom (r.hom y) = c y := congrArg (fun f => f.hom y) hrc
    exact (RingHom.mem_ker).mpr (e.trans (hc y hy))
  exact hker hxJ

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.gen :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] (z : X), s.base z = IsLocalRing.closedPoint R →
      (∀ z' : X, s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (T : Type) [CommRing T] [IsLocalRing T] (v : Sp T ⟶ X) (c : R →+* T),
      v.base (IsLocalRing.closedPoint T) = z → v ≫ s = spMap c → (∀ x ∈ IsLocalRing.maximalIdeal R, c x = 0) →
      ∃ τ : X.residueField z →+* T, spMap τ ≫ X.fromSpecResidueField z = v := by
  intro R _ _ _ X s _ z _ hmax T _ _ v c hv hvs hc
  subst hv
  have hφ : Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) ≫ X.fromSpecStalk _ = v :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of T) v
  have hk := kills_max R X s _ hmax T (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v) c
    (by rw [← Category.assoc, hφ]; exact hvs) hc
  refine ⟨Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk, ?_⟩
  have e : X.residue _ ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (Scheme.stalkClosedPointTo (R := CommRingCat.of T) v).hom hk) =
      Scheme.stalkClosedPointTo (R := CommRingCat.of T) v := by
    ext x
    rfl
  show Spec.map _ ≫ Spec.map (X.residue _) ≫ X.fromSpecStalk _ = v
  rw [← Spec.map_comp_assoc]
  exact (congrArg (fun g => Spec.map g ≫ X.fromSpecStalk _) e).trans hφ
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem UpperTheory.Gal.Ord.eq_one_of_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') (x₀ : Over.mk y' ⟶ G) (hx : x₀.left = (1 : T ⟶ G').left ≫ φ) : x₀ = 1 := by
  subst hy
  have h2 := h.2 T 1 1 x₀ x₀ hx hx
  have hsq : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one, hx]
  exact mul_eq_left.mp hsq

private theorem UpperTheory.Gal.Ord.one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') : (1 : Over.mk y' ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk y').hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    exact hy
  have e := eq_one_of_left h T hy (Over.homMk ((1 : T ⟶ G').left ≫ φ) hw) rfl
  rw [← e]
  rfl

private theorem UpperTheory.Gal.Ord.killedBy_iff {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (v : Ideal (𝓞 D.F)) (T : Over S') {y' : T.left ⟶ S} (hy : T.hom ≫ f = y')
    (x : T ⟶ o'.A) (x₀ : Over.mk y' ⟶ o.A) (hx : x₀.left = x.left ≫ m.φ) :
    KilledBy o v x₀ ↔ KilledBy o' v x := by
  have key : ∀ c : D.O, (x₀ ≫ o.act.act c).left = (x ≫ o'.act.act c).left ≫ m.φ := by
    intro c
    rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, m.act c]
  unfold KilledBy
  constructor
  · intro H a ha
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [← key, H a ha]
      exact one_left m.cart T hy
    · simp only [Over.w]
  · intro H a ha
    apply eq_one_of_left m.cart T hy
    rw [key, H a ha]

theorem UpperTheory.Gal.Ord.ordPull :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F))
      (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (s₀ : Sp k ⟶ Sp R) (o₀ : Obj b N s₀), ObjMap o₀ o y → IsWOrd o₀ w (𝟙 (Sp k)) → IsWOrd o w y := by
  intro p _ D R _ b N S s o w k _ _ y s₀ o₀ m h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [← h4]
  have hy : (Over.mk (𝟙 (Sp k))).hom ≫ y = y := by simp
  apply Nat.card_congr
  exact
    { toFun := fun g =>
        ⟨Over.homMk (m.cart.1.lift g.1.left (𝟙 _) (by simp)) (by rw [IsPullback.lift_snd]; rfl),
          (killedBy_iff m w _ hy _ g.1 (m.cart.1.lift_fst _ _ _).symm).mp g.2⟩
      invFun := fun g =>
        ⟨Over.homMk (g.1.left ≫ m.φ) (by rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; simp),
          (killedBy_iff m w _ hy g.1 _ rfl).mpr g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        apply m.cart.1.hom_ext
        · simp
        · simp }
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.factor :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
      ∀ (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (g : S'' ⟶ S'),
      f ≫ s = s' → g ≫ s' = s'' → ObjMap o' o f → ObjMap o'' o (g ≫ f) → Nonempty (ObjMap o'' o' g) := by
  intro p _ D R _ b N hN hNp S S' S'' s s' s'' o o' o'' f g hf hg m1 m2
  have hw : m2.φ ≫ o.A.hom = (o''.A.hom ≫ g) ≫ f := by
    rw [m2.cart.1.w, Category.assoc]
  let φ' : o''.A.left ⟶ o'.A.left := m1.cart.1.lift m2.φ (o''.A.hom ≫ g) hw
  have h1 : φ' ≫ m1.φ = m2.φ := m1.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ o'.A.hom = o''.A.hom ≫ g := m1.cart.1.lift_snd _ _ _
  let φ₂' : (G2 o''.A).left ⟶ (G2 o'.A).left :=
    pullback.lift (pullback.fst _ _ ≫ φ') (pullback.snd _ _ ≫ φ')
      (by simp only [Category.assoc, h2]; rw [pullback.condition_assoc])
  have sq : Geo.Tor.IsSquare φ' φ₂' := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h3 : φ₂' ≫ m1.φ₂ = m2.φ₂ := by
    apply pullback.hom_ext
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (fst o.A o.A) = m2.φ₂ ≫ Over.Hom.left (fst o.A o.A)
      rw [m1.sq.1, m2.sq.1, ← Category.assoc, sq.1, Category.assoc, h1]
    · change φ₂' ≫ m1.φ₂ ≫ Over.Hom.left (snd o.A o.A) = m2.φ₂ ≫ Over.Hom.left (snd o.A o.A)
      rw [m1.sq.2, m2.sq.2, ← Category.assoc, sq.2, Category.assoc, h1]
  have cart : IsGrpPullback o''.A o'.A g φ' := by
    refine IsGrpPullback.cancel m1.cart ?_ h2
    rw [h1]
    exact m2.cart
  have pol : LBIso o''.P (o'.P.pull φ₂') := by
    rw [← GlobalTheory.CechPic.cls_eq_iff o''.isLB (pull_isLB o'.isLB φ₂'), GlobalTheory.CechPic.cls_pull o'.isLB,
      ← Rigid.pull_cls_P m1, ← GlobalTheory.CechPic.pull_comp, h3, Rigid.pull_cls_P m2]
  have act : ∀ c : D.O, Over.Hom.left (o''.act.act c) ≫ φ' = φ' ≫ Over.Hom.left (o'.act.act c) := by
    intro c
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, reassoc_of% h1, h1, m1.act c, m2.act c]
    · simp only [Category.assoc, h2, Over.w_assoc, Over.w]
  have eta : ∀ y : D.La, Over.Hom.left (o''.eta y) ≫ φ' = g ≫ Over.Hom.left (o'.eta y) := by
    intro y
    apply m1.cart.1.hom_ext
    · simp only [Category.assoc, h1, m2.eta y, m1.eta y]
    · simp [h2]
  exact ⟨⟨φ', φ₂', cart, sq, act, pol, eta⟩⟩
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem asIdeal_spMap {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  haveI := u.isPrime
  have hu : u.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  show Ideal.comap φ u.asIdeal = RingHom.ker φ
  rw [hu, RingHom.ker_eq_comap_bot]

private theorem charP_of_eq_closedPoint {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : Type} [Field k] (β : R →+* k) (u : Sp k)
    (h : (spMap β).base u = IsLocalRing.closedPoint R) : CharP k p := by
  have hk : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β u, h]
    rfl
  have h0 : (p : k) = 0 := by
    have hm : (p : R) ∈ RingHom.ker β := by
      rw [hk]
      exact hpR
    rw [RingHom.mem_ker, map_natCast] at hm
    exact hm
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

private theorem exists_absNorm_eq {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (w : Ideal (𝓞 F))
    (hw : w.IsPrime) (hp : (p : 𝓞 F) ∈ w) : w.IsMaximal ∧ ∃ f : ℕ, 0 < f ∧ Ideal.absNorm w = p ^ f := by
  have hne : w ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  haveI : w.IsMaximal := hw.isMaximal hne
  refine ⟨inferInstance, ?_⟩
  obtain ⟨q, n, hn, hqw, hq, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow w
  have hqp : q = p := by
    by_contra hne'
    have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out hq).mpr (Ne.symm hne')
    have h1 : (((Nat.gcd p q : ℕ) : ℤ) : 𝓞 F) ∈ w := by
      rw [Nat.gcd_eq_gcd_ab]
      push_cast
      exact w.add_mem (w.mul_mem_right _ hp) (w.mul_mem_right _ hqw)
    rw [hcop.gcd_eq_one, Nat.cast_one, Int.cast_one] at h1
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one w).mpr h1)
  exact ⟨n, hn, hqp ▸ hN⟩

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.ordGen :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), (IsLocalRing.maximalIdeal R).comap (b.t i) = w → ∀ (M : Model b N) (z : M.X), M.s.base z = IsLocalRing.closedPoint R → (∀ z' : M.X, M.s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ M.X), (∀ q, y.base q = z) → IsWOrd M.univ w y := by
  intro p _ D R _ _ _ _ b N hN hNp hpR hm i w hw M z hz hmin k _ _ y hy
  haveI : Smooth M.s := @SmoothOfRelativeDimension.smooth _ _ _ _ M.smooth
  set β : R →+* k := (Spec.preimage (y ≫ M.s)).hom with hβdef
  have hyβ : y ≫ M.s = spMap β := (Spec.map_preimage (y ≫ M.s)).symm
  have hβbase : (spMap β).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    rw [← hyβ]
    exact (congrArg M.s.base (hy _)).trans hz
  haveI hchar : CharP k p := charP_of_eq_closedPoint hpR β _ hβbase
  have hk : (p : k) = 0 := CharP.cast_eq_zero k p
  have hkerβ : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β (IsLocalRing.closedPoint k), hβbase]
    rfl
  have hkerw : RingHom.ker (β.comp (b.t i)) = w := by
    rw [← RingHom.comap_ker, hkerβ, hw]
  have hwP : w.IsPrime := by
    rw [← hkerw]
    exact RingHom.ker_isPrime _
  have hpw : (p : 𝓞 D.F) ∈ w := by
    rw [← hkerw, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast]
    exact hk
  obtain ⟨hwM, f, hf, hnorm⟩ := exists_absNorm_eq w hwP hpw
  obtain ⟨π⟩ := par p D.F w f hwM hpw hf
  obtain ⟨o₀, ⟨a₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp k) M.s (spMap β) y hyβ M.univ
  apply ordPull p D R b N M.X M.s M.univ w k y (spMap β) o₀ a₀
  rcases point p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π with hW | hNO
  · exact hW
  exfalso
  have hLin := lin p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact hnorm
  obtain ⟨x, hxε, hxg, y0, hy0, hxy0⟩ :=
    alg2 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) _ (coh o₀) (PrimitiveSubmodule o₀.A) _ hLin
  have hxFil : x ∈ Fil o₀.A := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [← hxε c]
    have hle : Submodule.span k (Set.range fun c' => (coh o₀ π.g) ((⇑(frobDR p k hk o₀.A))^[f] c')) ≤
        LinearMap.ker x := by
      rw [Submodule.span_le]
      rintro _ ⟨c', rfl⟩
      exact hxg c'
    exact hle (hNO c hc)
  have hhom : hom o₀ π.ε x = x := by
    apply LinearMap.ext
    intro c
    exact hxε c
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k (spMap β) o₀
  obtain ⟨g, hKS, hgx⟩ :=
    ks p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π φ hφ x hxFil hhom ⟨y0, hy0, hxy0⟩
  obtain ⟨o', m', hlift⟩ := GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k (spMap β) o₀ β rfl φ hφ g hKS
  have hfst : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext a
    rfl
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← GlobalTheory.Cris.spMap_comp, hfst]
    show Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨v, ⟨hv1, ⟨av⟩⟩, -⟩ := M.rep (Sp (DualNumber k)) _ o'
  have hcompv : Nonempty (ObjMap o₀ M.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) :=
    (GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N _ _ _ _ _ _ M.univ o' o₀ v _).1 ⟨m'⟩ ⟨av⟩
  have hyv : y = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v := by
    apply (M.rep (Sp k) (spMap β) o₀).unique ⟨hyβ, ⟨a₀⟩⟩ ⟨?_, hcompv⟩
    rw [Category.assoc, hv1, ← Category.assoc, hcomp, Category.id_comp]
  have hcl : (spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (DualNumber k) := by
    apply PrimeSpectrum.ext
    refine (asIdeal_spMap (TrivSqZeroExt.fstHom k k k).toRingHom (IsLocalRing.closedPoint k)).trans ?_
    exact IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩))
  have hvz : v.base (IsLocalRing.closedPoint (DualNumber k)) = z := by
    rw [← hcl]
    have h1 := hy (IsLocalRing.closedPoint k)
    rw [hyv] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := gen R M.X M.s z hz hmin k y β (hy _) hyβ (fun r hr => by
    have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
    exact RingHom.mem_ker.mp hr')
  obtain ⟨τ, hτ⟩ := gen R M.X M.s z hz hmin (DualNumber k) v ((algebraMap k (DualNumber k)).comp β) hvz
    (hv1.trans (GlobalTheory.Cris.spMap_comp β _).symm) (fun r hr => by
      have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hr', map_zero])
  obtain ⟨oκ, ⟨aκ⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X _ M.s (M.X.fromSpecResidueField z ≫ M.s)
    (M.X.fromSpecResidueField z) rfl M.univ
  have a₀' : ObjMap o₀ M.univ (spMap σ ≫ M.X.fromSpecResidueField z) := by
    rw [hσ]
    exact a₀
  have av' : ObjMap o' M.univ (spMap τ ≫ M.X.fromSpecResidueField z) := by
    rw [hτ]
    exact av
  obtain ⟨b₀⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o₀ (M.X.fromSpecResidueField z) (spMap σ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hσ).trans hyβ)) aκ a₀'
  obtain ⟨b'⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o' (M.X.fromSpecResidueField z) (spMap τ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hτ).trans hv1)) aκ av'
  have hκ : (p : M.X.residueField z) = 0 :=
    σ.injective (by rw [map_natCast, map_zero]; exact hk)
  have hT : (p : DualNumber k) = 0 := by
    rw [← map_natCast (algebraMap k (DualNumber k)), hk, map_zero]
  have hNO' := desc p D R b N w f π _ k (DualNumber k) hκ hk hT σ τ _ _ _ oκ o₀ o' b₀ b' hNO
  have h0 := estep p D R b N w f hf π k hk hT (spMap β) _ o₀ o' m' hNO' x hxg
  rw [hhom] at h0
  have hmem := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hxFil (g x) 0 (hlift x hxFil)).mp h0
  have hneg := (Fil o₀.A).neg_mem hmem
  rw [zero_sub, neg_neg] at hneg
  exact hgx hneg
end
