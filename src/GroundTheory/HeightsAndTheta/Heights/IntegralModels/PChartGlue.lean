import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section ChartLoc

variable {Ω : Type*} [Field Ω] {τ : Type*} (x : τ → Ω) (i : τ)

theorem intCast_mem_chartRing (R : Type*) [CommRing R] [Algebra R Ω] (z : ℤ) :
    (z : Ω) ∈ chartRing R x i :=
  intCast_mem _ z

theorem mem_chartRing_of_int (R : Type*) [CommRing R] [Algebra R Ω] {y : Ω}
    (hy : y ∈ chartRing ℤ x i) : y ∈ chartRing R x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap z => simp [intCast_mem_chartRing x i R z]
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

variable (R : Type*) [CommRing R] [Algebra ℤ R] (T : Submonoid ℤ) [IsLocalization T R] [Algebra R Ω]

omit [IsLocalization T R] in
theorem algebraMap_algebraMap_int (z : ℤ) : algebraMap R Ω (algebraMap ℤ R z) = z := by
  rw [eq_intCast (algebraMap ℤ R), map_intCast]

theorem inv_mem_chartRing_loc {t : ℤ} (ht : t ∈ T) :
    (t : Ω) ≠ 0 ∧ (t : Ω)⁻¹ ∈ chartRing R x i := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨t, ht⟩ : T)
  have h1 : algebraMap R Ω (↑u⁻¹ : R) * (t : Ω) = 1 := by
    rw [← algebraMap_algebraMap_int R t]
    have : algebraMap ℤ R t = (u : R) := hu.symm
    rw [this, ← map_mul, Units.inv_mul, map_one]
  have ht0 : (t : Ω) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨ht0, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Subalgebra.algebraMap_mem _ _

theorem exists_mul_mem_chartRing_int {y : Ω} (hy : y ∈ chartRing R x i) :
    ∃ t ∈ T, (t : Ω) * y ∈ chartRing ℤ x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_mem T, by rw [Int.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective T r
    refine ⟨s, s.2, ?_⟩
    have h := congrArg (algebraMap R Ω) (IsLocalization.mk'_spec R a s)
    rw [map_mul, algebraMap_algebraMap_int, algebraMap_algebraMap_int] at h
    rw [mul_comm, h]
    exact intCast_mem_chartRing x i ℤ a
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y + z) = (t' : Ω) * ((t : Ω) * y) + (t : Ω) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (intCast_mem_chartRing x i ℤ _) hty)
      (mul_mem (intCast_mem_chartRing x i ℤ _) htz)
  | mul y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y * z) = ((t : Ω) * y) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact mul_mem hty htz

theorem exists_mul_mem_chartRing_int_fin {ι : Type*} [Fintype ι] (y : ι → Ω)
    (hy : ∀ l, y l ∈ chartRing R x i) :
    ∃ t ∈ T, ∀ l, (t : Ω) * y l ∈ chartRing ℤ x i := by
  classical
  choose t ht hty using fun l => exists_mul_mem_chartRing_int x i R T (hy l)
  refine ⟨∏ l, t l, prod_mem fun l _ => ht l, fun l => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul, mul_comm (t l : Ω),
    mul_assoc]
  exact mul_mem (intCast_mem_chartRing x i ℤ _) (hty l)

end ChartLoc

theorem intCast_not_mem_of_not_dvd {A : Type*} [CommRing A] {Q : Ideal A} (hQ : Q ≠ ⊤) {p : ℕ}
    (hp : p.Prime) (hpQ : (p : A) ∈ Q) {s : ℤ} (hs : ¬ (p : ℤ) ∣ s) : (s : A) ∉ Q := by
  intro hsQ
  have hcop : IsCoprime (p : ℤ) s := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
    simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
  obtain ⟨u, v, huv⟩ := hcop
  have h1 := congrArg (Int.cast : ℤ → A) huv
  push_cast at h1
  apply hQ
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hsQ)

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section Generic

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

end Generic

section Glue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]

abbrev primeTo (p : Nat.Primes) : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl

theorem mem_primeTo {p : Nat.Primes} {s : ℤ} : s ∈ primeTo p ↔ ¬ ((p : ℕ) : ℤ) ∣ s := by
  show s ∉ Ideal.span _ ↔ _
  rw [Ideal.mem_span_singleton]

instance (p : S) : IsLocalization (primeTo (p : Nat.Primes)) (o p) := inferInstance

variable (x) in

theorem inv_mem_chartRing_at (p : S) (i : τ) {s : ℤ} (hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s) :
    (s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ chartRing (o p) x i :=
  inv_mem_chartRing_loc x i (o p) (primeTo (p : Nat.Primes)) (mem_primeTo.2 hs)

variable (x o₀) in

theorem inv_prod_mem_chartRing (i : τ) :
    ((primeProd S : ℤ) : Ω) ≠ 0 ∧ ((primeProd S : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i :=
  inv_mem_chartRing_loc x i o₀ (Submonoid.powers (primeProd S)) (Submonoid.mem_powers _)

def primeProdErase (S : Finset Nat.Primes) (p : Nat.Primes) : ℤ := ∏ q ∈ S.erase p, ((q : ℕ) : ℤ)

theorem primeProd_eq_mul {p : Nat.Primes} (hp : p ∈ S) :
    primeProd S = ((p : ℕ) : ℤ) * primeProdErase S p :=
  (Finset.mul_prod_erase S (fun q : Nat.Primes => ((q : ℕ) : ℤ)) hp).symm

theorem dvd_primeProd {p : Nat.Primes} (hp : p ∈ S) : ((p : ℕ) : ℤ) ∣ primeProd S :=
  ⟨_, primeProd_eq_mul hp⟩

theorem dvd_primeProdErase {p q : Nat.Primes} (hq : q ∈ S) (hqp : q ≠ p) :
    ((q : ℕ) : ℤ) ∣ primeProdErase S p :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hqp, hq⟩)

theorem not_dvd_primeProdErase (p : Nat.Primes) : ¬ ((p : ℕ) : ℤ) ∣ primeProdErase S p := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp p.2) _).1 h
  have : (p : ℕ) = q := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (Int.natCast_dvd_natCast.1 hpq)
  exact (Finset.mem_erase.1 hq).1 (Subtype.ext this).symm


variable (x o₀) in

theorem inv_prime_mem_chartRing {p : Nat.Primes} (hp : p ∈ S) (i : τ) :
    (((p : ℕ) : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i := by
  obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  have h : (((p : ℕ) : ℤ) : Ω)⁻¹ = (primeProdErase S p : Ω) * ((primeProd S : ℤ) : Ω)⁻¹ := by
    rw [primeProd_eq_mul hp] at hm0 ⊢
    push_cast at hm0 ⊢
    have h1 : ((p : ℕ) : Ω) ≠ 0 := fun h => hm0 (by rw [h, zero_mul])
    have h2 : (primeProdErase S p : Ω) ≠ 0 := fun h => hm0 (by rw [h, mul_zero])
    field_simp
  rw [h]
  exact mul_mem (intCast_mem_chartRing x i o₀ _) hm

theorem smul_mem_of_chart {R : Type*} [CommRing R] [Algebra R Ω] (B : ChartBundle R x r E) {i : τ}
    {a : Ω} (ha : a ∈ chartRing R x i) {e : E} (he : e ∈ B.lat i) : a • e ∈ B.lat i :=
  B.stable i a ha e he

theorem intCast_smul_mem {R : Type*} [CommRing R] [Algebra R Ω] (B : ChartBundle R x r E) {i : τ}
    (z : ℤ) {e : E} (he : e ∈ B.lat i) : (z : Ω) • e ∈ B.lat i :=
  B.stable i _ (intCast_mem_chartRing x i R z) e he

variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)

def glueLat (i : τ) : AddSubgroup E := B₀.lat i ⊓ ⨅ p, (Bp p).lat i

theorem mem_glueLat {i : τ} {e : E} :
    e ∈ glueLat B₀ Bp i ↔ e ∈ B₀.lat i ∧ ∀ p, e ∈ (Bp p).lat i := by
  simp [glueLat, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]

variable {B₀ Bp}

theorem exists_prime_pow_smul_mem {i : τ} (p : S)
    (hSR : SameRationalSpan (B₀.lat i) ((Bp p).lat i)) {w : E} (hw : w ∈ B₀.lat i) :
    ∃ k : ℕ, ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w ∈ (Bp p).lat i := by
  obtain ⟨N, hN0, hN⟩ := hSR.1 w hw
  obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
    (p : Nat.Primes).2.one_lt.ne'
  refine ⟨k, ?_⟩
  have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' : ℤ) := fun h => hn' (Int.natCast_dvd_natCast.1 h)
  obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
  have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w = ((n' : ℤ) : Ω)⁻¹ • ((N : Ω) • w) := by
    rw [smul_smul, hN']
    congr 1
    push_cast at hs0 ⊢
    field_simp
  rw [this, Nat.cast_smul_eq_nsmul]
  exact smul_mem_of_chart (Bp p) hsinv hN

theorem exists_pow_smul_mem_all {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i))
    {w : E} (hw : w ∈ B₀.lat i) (z : ℤ) (P : S → Prop)
    (hz : ∀ p, P p → (((p : Nat.Primes) : ℕ) : ℤ) ∣ z) :
    ∃ K : ℕ, ∀ K' ≥ K, ∀ p, P p → ((z : Ω) ^ K') • w ∈ (Bp p).lat i := by
  classical
  choose k hk using fun p => exists_prime_pow_smul_mem p (hSR p) hw
  refine ⟨Finset.univ.sup k, fun K' hK' p hp => ?_⟩
  obtain ⟨c, hc⟩ := hz p hp
  have hle : k p ≤ K' := le_trans (Finset.le_sup (Finset.mem_univ p)) hK'
  have : ((z : Ω) ^ K') • w =
      ((z : Ω) ^ (K' - k p) * (c : Ω) ^ k p) • ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k p • w := by
    rw [smul_smul]
    congr 1
    rw [hc, Int.cast_mul, mul_assoc, ← mul_pow, mul_comm (c : Ω), ← Int.cast_mul, ← hc,
      pow_sub_mul_pow _ hle]
  rw [this]
  exact smul_mem_of_chart (Bp p) (mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _)
    (pow_mem (intCast_mem_chartRing x i _ _) _)) (hk p)

theorem mem_B₀_iff {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (v : E) :
    v ∈ B₀.lat i ↔ ∃ n : ℕ, primeProd S ^ n • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hv (primeProd S) (fun _ => True)
      (fun p _ => dvd_primeProd p.2)
    refine ⟨K, (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hv
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact hK K le_rfl p trivial
  · rintro ⟨n, hn⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hn).1
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at h0
    obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
    have : v = (((primeProd S : ℤ) : Ω)⁻¹) ^ n • (((primeProd S : ℤ) : Ω) ^ n • v) := by
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hm0, one_pow, one_smul]
    rw [this]
    exact smul_mem_of_chart B₀ (pow_mem hm _) h0

theorem mem_Bp_iff [CharZero Ω] {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (p : S) (v : E) :
    v ∈ (Bp p).lat i ↔ ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨N, hN0, hN⟩ := (hSR p).2 v hv
    obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
      (p : Nat.Primes).2.one_lt.ne'
    have hw : ((n' : ℤ) : Ω) • v ∈ B₀.lat i := by
      have : ((n' : ℤ) : Ω) • v =
          ((((p : Nat.Primes) : ℕ) : ℤ) : Ω)⁻¹ ^ k • ((N : Ω) • v) := by
        rw [smul_smul, hN']
        congr 1
        have : (((p : Nat.Primes) : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (p : Nat.Primes).2.ne_zero
        push_cast
        rw [inv_pow, mul_comm ((((p : Nat.Primes) : ℕ) : Ω) ^ k), ← mul_assoc, mul_comm _ (n' : Ω),
          mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ this), mul_one]
      rw [this, Nat.cast_smul_eq_nsmul]
      exact smul_mem_of_chart B₀ (pow_mem (inv_prime_mem_chartRing x o₀ p.2 i) _) hN
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hw (primeProdErase S p) (fun q => q ≠ p)
      (fun q hq => dvd_primeProdErase q.2 (fun h => hq (Subtype.ext h)))
    have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' * primeProdErase S p ^ K) := by
      rw [(Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_mul]
      rintro (h | h)
      · exact hn' (Int.natCast_dvd_natCast.1 h)
      · exact not_dvd_primeProdErase _ ((Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_of_dvd_pow h)
    refine ⟨n' * primeProdErase S p ^ K, hs, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω]
    have heq : (((n' * primeProdErase S p ^ K : ℤ)) : Ω) • v =
        ((primeProdErase S p : Ω) ^ K) • (((n' : ℤ) : Ω) • v) := by
      rw [smul_smul]; congr 1; push_cast; ring
    refine (mem_glueLat B₀ Bp).2 ⟨?_, fun q => ?_⟩
    · rw [heq]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hw
    · by_cases hq : q = p
      · subst hq
        exact intCast_smul_mem (Bp q) _ hv
      · rw [heq]
        exact hK K le_rfl q hq
  · rintro ⟨s, hs, hsv⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hsv).2 p
    rw [← Int.cast_smul_eq_zsmul Ω] at h0
    obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
    have : v = ((s : Ω)⁻¹) • ((s : Ω) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact smul_mem_of_chart (Bp p) hsinv h0

theorem glueLat_stable (i : τ) (a : Ω) (ha : a ∈ chartRing ℤ x i) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : a • e ∈ glueLat B₀ Bp i := by
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  exact (mem_glueLat B₀ Bp).2 ⟨B₀.stable i a (mem_chartRing_of_int x i o₀ ha) e h0,
    fun p => (Bp p).stable i a (mem_chartRing_of_int x i (o p) ha) e (hp p)⟩

theorem glueLat_overlap (i j : τ) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ glueLat B₀ Bp j := by
  classical
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  obtain ⟨m₀, hm₀⟩ := B₀.overlap i j hi hj e h0
  choose mp hmp using fun p => (Bp p).overlap i j hi hj e (hp p)
  refine ⟨max m₀ (Finset.univ.sup mp), (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
  · rw [← pow_sub_mul_pow _ (le_max_left m₀ (Finset.univ.sup mp)), mul_smul]
    exact smul_mem_of_chart B₀ (pow_mem (div_mem_chartRing x j i) _) hm₀
  · have hle : mp p ≤ max m₀ (Finset.univ.sup mp) :=
      le_trans (Finset.le_sup (Finset.mem_univ p)) (le_max_right _ _)
    rw [← pow_sub_mul_pow _ hle, mul_smul]
    exact smul_mem_of_chart (Bp p) (pow_mem (div_mem_chartRing x j i) _) (hmp p)

end Glue

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section FrameGeneric

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

def IsFrameAt (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E) (h : Ω) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, h ^ n • e ∈ M) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, h ^ n * a q ∈ A) ∧ e = ∑ q, a q • b q

theorem exists_frame_cover (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E)
    (hloc : ∀ Q : Ideal A, Q.IsMaximal →
      ∃ h : Ω, ∃ hh : h ∈ A, (⟨h, hh⟩ : A) ∉ Q ∧ IsFrameAt A r M h) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ A) ∧ (∀ l, c l ∈ A) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, IsFrameAt A r M (f l) := by
  let H : Set A := {h | IsFrameAt A r M h}
  have htop : Ideal.span H = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hh, hQh, hfr⟩ := hloc Q hQ
    exact hQh (hle (Ideal.subset_span (show (⟨h, hh⟩ : A) ∈ H from hfr)))
  have h1 : (1 : A) ∈ Ideal.span H := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, c, g, hcg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : A) : Ω), fun l => (c l : Ω), fun l => (g l : A).2, fun l => (c l).2,
    ?_, fun l => (g l).2⟩
  have := congrArg Subtype.val hcg
  simpa using this

theorem mem_ideal_of_sum {A : Subalgebra ℤ Ω} (Q : Ideal A) {k : ℕ} (a y : Fin k → Ω)
    (ha : ∀ l, a l ∈ A) (hy : ∀ l, y l ∈ A) (hyQ : ∀ l, (⟨y l, hy l⟩ : A) ∈ Q) {z : Ω}
    (hz : z ∈ A) (hsum : ∑ l, a l * y l = z) : (⟨z, hz⟩ : A) ∈ Q := by
  have : (⟨z, hz⟩ : A) = ∑ l, (⟨a l, ha l⟩ : A) * ⟨y l, hy l⟩ := Subtype.ext (by simp [← hsum])
  rw [this]
  exact Q.sum_mem fun l _ => Q.mul_mem_left _ (hyQ l)

theorem intCast_subtype (A : Subalgebra ℤ Ω) (z : ℤ) :
    (⟨(z : Ω), intCast_mem A z⟩ : A) = (z : A) :=
  Subtype.ext (by simp)

theorem mem_of_prime_pow_mul_mem {A : Subalgebra ℤ Ω} {p : ℕ} (hp : p.Prime) {s : ℤ}
    (hs : ¬ (p : ℤ) ∣ s) (N : ℕ) {y : Ω} (h1 : (((p : ℤ) : Ω)) ^ N * y ∈ A)
    (h2 : (s : Ω) * y ∈ A) : y ∈ A := by
  have hcop : IsCoprime ((p : ℤ) ^ N) s := by
    have : IsCoprime (p : ℤ) s := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
      simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    exact this.pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have : y = (u : Ω) * ((((p : ℤ) : Ω)) ^ N * y) + (v : Ω) * ((s : Ω) * y) := by
    have h := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at h ⊢
    linear_combination (-y) * h
  rw [this]
  exact add_mem (mul_mem (intCast_mem A u) h1) (mul_mem (intCast_mem A v) h2)

end FrameGeneric

section FrameGlue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem frame_away {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∉ Q) :
    ∃ h : Ω, ∃ hh : h ∈ chartRing ℤ x i, (⟨h, hh⟩ : chartRing ℤ x i) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  set m : ℤ := primeProd S with hm
  obtain ⟨hm0, hminv⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B₀.frame i hi
  obtain ⟨t, ht, htf⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) f hf
  obtain ⟨t', ht', htc⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) c hc
  obtain ⟨J, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
  obtain ⟨J', rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht'
  have hmA : (m : Ω) ∈ chartRing ℤ x i := intCast_mem (chartRing ℤ x i) m
  have hJ : ∀ l, (m : Ω) ^ J * f l ∈ chartRing ℤ x i := fun l => by simpa using htf l
  have hφ : ∀ l, (m : Ω) ^ (J + 1) * f l ∈ chartRing ℤ x i := fun l => by
    have : (m : Ω) ^ (J + 1) * f l = (m : Ω) * ((m : Ω) ^ J * f l) := by ring
    rw [this]; exact mul_mem hmA (hJ l)
  have hex : ∃ l, (⟨(m : Ω) ^ (J + 1) * f l, hφ l⟩ : chartRing ℤ x i) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => ((m ^ J' : ℤ) : Ω) * c l)
      (fun l => (m : Ω) ^ (J + 1) * f l) htc hφ hall (z := ((m ^ (J + 1 + J') : ℤ) : Ω))
      (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, ((m ^ J' : ℤ) : Ω) * c l * ((m : Ω) ^ (J + 1) * f l) =
            ((m : Ω) ^ J' * (m : Ω) ^ (J + 1)) * ∑ l, c l * f l := by
          rw [Finset.mul_sum]; push_cast; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    push_cast at hmem
    exact hmQ (hQ.mem_of_pow_mem _ hmem)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  refine ⟨_, hφ l, hl, b, hli, hsp, fun e => ?_⟩
  have hYX : ∀ v ∈ B₀.lat i, ∃ k : ℕ, (m : Ω) ^ k • v ∈ glueLat B₀ Bp i := fun v hv => by
    obtain ⟨n, hn⟩ := (mem_B₀_iff hSR v).1 hv
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at hn
    exact ⟨n, hn⟩
  rw [exists_pow_smul_mem_iff_of_loc (chartRing ℤ x i) (glueLat B₀ Bp i) (B₀.lat i) J hm0 hmA (hJ l)
    (glueLat_stable i) (fun e he => ((mem_glueLat B₀ Bp).1 he).1)
    (fun e he => smul_mem_of_chart B₀ hminv he) hYX e, hiff e]
  refine exists_congr fun a => and_congr (forall_congr' fun q => ?_) Iff.rfl
  have key := exists_pow_smul_mem_iff_of_loc (E := Ω) (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
    (chartRing o₀ x i).toSubring.toAddSubgroup J hm0 hmA (hJ l)
    (fun a ha e he => show a * e ∈ chartRing ℤ x i from mul_mem ha he) (fun y hy => mem_chartRing_of_int x i o₀ hy)
    (fun y hy => show _ * y ∈ chartRing o₀ x i from mul_mem hminv hy)
    (fun y hy => by
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_chartRing_int x i o₀ (Submonoid.powers m) hy
      obtain ⟨K, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
      exact ⟨K, by simpa using hty⟩) (a q)
  simpa [smul_eq_mul] using key.symm

end FrameGlue

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

theorem repr_of_eq_sum {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {b : Fin r → E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) {e : E} {a : Fin r → Ω} (hae : e = ∑ q, a q • b q)
    (q : Fin r) : (Module.Basis.mk hli hsp.ge).repr e q = a q := by
  have : e = ∑ q, a q • (Module.Basis.mk hli hsp.ge) q := by simpa [Module.Basis.coe_mk] using hae
  rw [this, (Module.Basis.mk hli hsp.ge).repr_sum_self a]

section FrameGlueP

variable {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem frame_at_prime {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (p : S) (hpQ : ((((p : Nat.Primes) : ℕ) : ℤ) : (chartRing ℤ x i)) ∈ Q) :
    ∃ h : Ω, ∃ hh : h ∈ (chartRing ℤ x i), (⟨h, hh⟩ : (chartRing ℤ x i)) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  have hPp : Prime (((p : Nat.Primes) : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (p : Nat.Primes).2
  have hnot : ∀ {s : ℤ}, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s → (s : (chartRing ℤ x i)) ∉ Q := fun hs =>
    intCast_not_mem_of_not_dvd hQ.ne_top (p : Nat.Primes).2 (by simpa using hpQ) hs
  obtain ⟨k, g, d, hg, hd, hsum, hb⟩ := (Bp p).frame i hi
  obtain ⟨t, ht, htg⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) g hg
  obtain ⟨t', ht', htd⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) d hd
  have hex : ∃ l, (⟨(t : Ω) * g l, htg l⟩ : (chartRing ℤ x i)) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => (t' : Ω) * d l) (fun l => (t : Ω) * g l) htd htg hall
      (z := ((t' * t : ℤ) : Ω)) (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, (t' : Ω) * d l * ((t : Ω) * g l) = ((t' : Ω) * t) * ∑ l, d l * g l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    exact hnot (mem_primeTo.1 (mul_mem ht' ht)) hmem
  obtain ⟨l, hl⟩ := hex
  have hγA : (t : Ω) * g l ∈ (chartRing ℤ x i) := htg l
  obtain ⟨b, hli, hsp, hiff⟩ := hb l

  have hγpow : ∀ (n : ℕ) {y : Ω}, g l ^ n * y ∈ chartRing (o p) x i →
      ((t : Ω) * g l) ^ n * y ∈ chartRing (o p) x i := fun n y hy => by
    rw [mul_pow, mul_assoc]; exact mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _) hy
  have hsingle : ∀ q q' : Fin r, ∃ n : ℕ, g l ^ n * (Pi.single q (1 : Ω) : Fin r → Ω) q' ∈
      chartRing (o p) x i := fun q q' => ⟨0, by
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩

  obtain ⟨σ₁, hσ₁, n₁, hC1⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ q, ∀ n' ≥ n,
      ((σ : Ω) * ((t : Ω) * g l) ^ n') • b q ∈ glueLat B₀ Bp i := by
    refine exists_uniform_mul _ (chartRing ℤ x i) (glueLat B₀ Bp i) (glueLat_stable i) hγA b fun q => ?_
    obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, hsingle q, by simp [Pi.single_apply]⟩
    have hγn : ((t : Ω) * g l) ^ n • b q ∈ (Bp p).lat i := by
      rw [mul_pow, mul_smul]
      exact smul_mem_of_chart (Bp p) (pow_mem (intCast_mem_chartRing x i _ _) _) hn
    obtain ⟨s, hs, hsm⟩ := (mem_Bp_iff hSR p _).1 hγn
    refine ⟨s, mem_primeTo.2 hs, n, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω, smul_smul] at hsm
    exact hsm
  let bb := Module.Basis.mk hli hsp.ge
  have hbb : ∀ q, bb q = b q := fun q => by simp [bb, Module.Basis.coe_mk]

  obtain ⟨K₀, Gn, hG, hGspan⟩ := chartBundle_exists_gens B₀ hi

  obtain ⟨σ₂, hσ₂, n₂, hC2⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ,
      ∀ jq : (Fin K₀ × Fin r) × Fin r, ∀ n' ≥ n,
        ((σ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n') • bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i).toSubring.toAddSubgroup := by
    refine exists_uniform_mul (E := Ω) _ (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
      (fun a ha e he => show a * e ∈ (chartRing ℤ x i) from mul_mem ha he)
      (mul_mem (intCast_mem (chartRing ℤ x i) _) hγA) _ fun jq => ?_
    obtain ⟨v, hv⟩ := exists_prime_pow_smul_mem p (hSR p) (hG jq.1)
    obtain ⟨a, ha, hae⟩ := (hiff (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v • Gn jq.1)).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
    have hq : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v * bb.repr (Gn jq.1) jq.2 = a jq.2 := by
      have := repr_of_eq_sum hli hsp hae jq.2
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    obtain ⟨n, hn⟩ := ha jq.2
    obtain ⟨s, hs, hsA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    refine ⟨s, hs, v + n, ?_⟩
    show (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i)
    have : (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 =
        (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ n * ((t : Ω) * g l) ^ v) * ((s : Ω) * (((t : Ω) * g l) ^ n * a jq.2)) := by
      rw [← hq]; ring
    rw [this]
    exact mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem hγA _)) hsA
  have hσ : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) := by
    rw [hPp.dvd_mul, hPp.dvd_mul]
    rintro ((h | h) | h)
    · exact mem_primeTo.1 hσ₁ h
    · exact mem_primeTo.1 hσ₂ h
    · exact not_dvd_primeProdErase _ h
  have hmPμ : ((primeProd S : ℤ) : Ω) = ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) := by
    rw [primeProd_eq_mul p.2, Int.cast_mul]
  have hhA : ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) ∈ (chartRing ℤ x i) :=
    mul_mem (intCast_mem (chartRing ℤ x i) _) hγA

  have hC3 : ∀ e ∈ glueLat B₀ Bp i, ∀ q, ∃ n : ℕ,
      (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n * bb.repr e q ∈ (chartRing ℤ x i) := by
    intro e he q
    obtain ⟨he0, hep⟩ := (mem_glueLat B₀ Bp).1 he
    obtain ⟨a, ha, hae⟩ := (hiff e).1 ⟨0, by simpa using hep p⟩
    have hra : bb.repr e q = a q := repr_of_eq_sum hli hsp hae q
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨se, hse, hseA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    obtain ⟨β, hβ, heβ⟩ := hGspan e he0
    obtain ⟨t₀, ht₀, ht₀β⟩ :=
      exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers (primeProd S)) β hβ
    obtain ⟨κ, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht₀
    have hrepr_e : bb.repr e q = ∑ j, β j * bb.repr (Gn j) q := by
      conv_lhs => rw [heβ]
      simp [map_sum, map_smul]
    have hii : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q) ∈ (chartRing ℤ x i) := by
      rw [hrepr_e, Finset.mul_sum, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      have h1 : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q ∈ (chartRing ℤ x i) := hC2 (j, q) n₂ le_rfl
      have h2 := ht₀β j
      have : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * (β j * bb.repr (Gn j) q)) =
          ((((primeProd S) ^ κ : ℤ) : Ω) * β j) *
            ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q) := by
        rw [Int.cast_pow]; ring
      rw [this]
      exact mul_mem h2 h1
    have hc1 : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) *
        ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((t : Ω) * g l) ^ n * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q)) := by
        rw [hmPμ]; ring
      rw [this]
      exact mul_mem (pow_mem hγA _) hii
    have hc2 : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ n₂) * ((se : Ω) * (((t : Ω) * g l) ^ n * a q)) := by
        rw [hra]; ring
      rw [this]
      exact mul_mem (mul_mem (mul_mem (intCast_mem (chartRing ℤ x i) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _))
        (pow_mem hγA _)) hseA
    have hc := mem_of_prime_pow_mul_mem (A := (chartRing ℤ x i)) (p : Nat.Primes).2 (mem_primeTo.1 hse)
      (n₂ + κ) hc1 hc2
    refine ⟨κ + n + n₂ + 1, ?_⟩
    have : (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (κ + n + n₂ + 1) *
        bb.repr e q = ((σ₁ : Ω) ^ (κ + n + n₂ + 1) * (σ₂ : Ω) ^ (κ + n + n₂) *
          ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n + n₂ + 1) * ((t : Ω) * g l) ^ (κ + 1)) *
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) := by
      rw [Int.cast_mul, Int.cast_mul]; ring
    rw [this]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
      (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hc

  have hhQ : (⟨_, hhA⟩ : (chartRing ℤ x i)) ∉ Q := by
    have : (⟨_, hhA⟩ : (chartRing ℤ x i)) =
        ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : (chartRing ℤ x i)) * ⟨_, hγA⟩ :=
      Subtype.ext (by simp)
    rw [this]
    intro hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact hnot hσ h
    · exact hl h
  refine ⟨_, hhA, hhQ, b, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩⟩
  · refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
    · obtain ⟨n', hn'⟩ := hC3 _ hn q
      refine ⟨n' + n, ?_⟩
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hn'
      exact hn'
    · conv_lhs => rw [← bb.sum_repr e]
      simp only [hbb]
  · choose nq hnq using ha
    refine ⟨Finset.univ.sup nq + (n₁ + 1), ?_⟩
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    set h := ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) with hh
    have hbq : h ^ (n₁ + 1) • b q ∈ glueLat B₀ Bp i := by
      have : h ^ (n₁ + 1) = ((σ₁ : Ω) ^ n₁ * ((σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n₁ + 1) *
          ((t : Ω) * g l)) * ((σ₁ : Ω) * ((t : Ω) * g l) ^ n₁) := by
        rw [hh]; push_cast; ring
      rw [this, mul_smul]
      exact glueLat_stable i _ (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
        (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) hγA) _ (hC1 q n₁ le_rfl)
    have haq : h ^ (Finset.univ.sup nq) * a q ∈ (chartRing ℤ x i) := by
      rw [← pow_sub_mul_pow h (Finset.le_sup (f := nq) (Finset.mem_univ q)), mul_assoc]
      exact mul_mem (pow_mem hhA _) (hnq q)
    have : h ^ (Finset.univ.sup nq + (n₁ + 1)) • (a q • b q) =
        (h ^ (Finset.univ.sup nq) * a q) • (h ^ (n₁ + 1) • b q) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact glueLat_stable i _ haq _ hbq

end FrameGlueP

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

theorem glueLat_frame {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
    {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
    {i : τ} (hi : x i ≠ 0) (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x i) ∧ (∀ l, c l ∈ chartRing ℤ x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) (f l) := by
  refine exists_frame_cover _ r _ fun Q hQ => ?_
  by_cases hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∈ Q
  · rw [primeProd, Int.cast_prod] at hmQ
    obtain ⟨p, hp, hpQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hQ.isPrime)).1 hmQ
    exact frame_at_prime hi hSR Q hQ.isPrime ⟨p, hp⟩ hpQ
  · exact frame_away hi hSR Q hQ.isPrime hmQ

theorem ChartGlue.proof : ChartGlue.Statement := by
  intro Ω _ _ τ _ x r E _ _ S o₀ _ _ _ _ o _ _ _ _ B₀ Bp hSR
  refine ⟨{ lat := glueLat B₀ Bp
            stable := glueLat_stable
            frame := fun i hi => glueLat_frame hi fun p => hSR p i hi
            overlap := glueLat_overlap }, fun i hi => ⟨mem_B₀_iff fun p => hSR p i hi,
              fun p v => mem_Bp_iff (fun p => hSR p i hi) p v⟩⟩

end GroundTheory.Heights₂.Heights.Model
end
