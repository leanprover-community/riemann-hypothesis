import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVolA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnifVSpec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensSAChar

section
noncomputable section

namespace PI.VolStabW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    nlinarith
  have hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
    intro w hw
    have := hsq w hw
    rw [sq, Complex.mul_re]
    nlinarith
  have hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hn k).le
  have key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, hre _ (hn k)]
      have h1 := h k
      have h2 := hle k
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]
  have hz1 : z.re ≤ 1 := by simpa using hle 0
  have hre1 : z.re = 1 := by
    by_contra hne
    have hε : 0 < 1 - z.re := by
      rcases lt_or_eq_of_le hz1 with h' | h'
      · linarith
      · exact absurd h' hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := key k
    have h2 := h k
    have h3 : 1 < (3 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have := hsq z hz
    rw [hre1] at this
    nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

variable {F : Type} [Field F] [NumberField F]

theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  filter_upwards [(I.finite_toSet).eventually_cofinite_notMem] with v hv
  have hbig : ∀ y ∈ v.adicCompletionIntegers F, 1 / 2 < (psiV F ψ v y).re := by
    intro y hy
    have hmem : Function.update x0 v ⟨y, hy⟩ ∈ (I : Set _).pi u := by
      intro w hw
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [Function.update_of_ne hwv]
      exact (hu w hw).2
    have e : Φ (Function.update x0 v ⟨y, hy⟩) = pairA F 0 (singleV F v y) := by
      show pairA F 0 _ = _
      congr 1
      apply RestrictedProduct.ext
      intro j
      show ((Function.update x0 v ⟨y, hy⟩ j : _) : Fv F j) =
        (Pi.single v y : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) j
      by_cases hj : j = v
      · subst hj
        simp
      · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    have := hsub hmem
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  refine eq_one_of_pow (psiV F ψ v y) (hψ.2.1 _) ?_
  intro k
  rw [← psiV_nsmul]
  apply hbig
  rw [nsmul_eq_mul]
  exact mul_mem (by exact_mod_cast (natCast_mem (v.adicCompletionIntegers F) (2 ^ k))) hy

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabW
end
end

section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom x
  obtain ⟨N, hN1, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F U (hU.mem_nhds U.zero_mem)
  obtain ⟨β, y, hy, hxy⟩ := PIW.AdelClassFin.DictRing.af_approx _ hmx (m * N)
    (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / (m : F), ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) :=
    (IsUnit.mk0 _ hmF).map _
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
      (N : FiniteAdeleRing (𝓞 F) F) * y := by
    apply hu.mul_left_cancel
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F) :=
      map_natCast _ m
    have e2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
        algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β := by
      rw [← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F]
    rw [mul_sub, e2, e1]
    rw [hxy]
    push_cast
    ring
  rw [key]
  exact hNU y hy

end PI.VolStabW
end
end

section
noncomputable section

namespace PI.VolStabW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

variable {F : Type} [Field F] [NumberField F]

theorem af_add (y z : Af F) (w : HeightOneSpectrum (𝓞 F)) : (y + z) w = y w + z w := rfl
theorem af_sub (y z : Af F) (w : HeightOneSpectrum (𝓞 F)) : (y - z) w = y w - z w := rfl
theorem af_neg (y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (-y) w = -y w := rfl
theorem af_zero (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := rfl

theorem adele_pairing_zero_add (y z : Af F) : pairA F 0 (y + z) = pairA F 0 y + pairA F 0 z := by
  show ((0 : Ainf F), y + z) = ((0 : Ainf F), y) + ((0 : Ainf F), z)
  rw [Prod.mk_add_mk, add_zero]

theorem pairA_nsmul0 (m : ℕ) (y : Af F) : pairA F 0 (m • y) = m • pairA F 0 y := by
  show ((0 : Ainf F), m • y) = m • ((0 : Ainf F), y)
  rw [Prod.smul_mk, smul_zero]

open Classical in
theorem singleV_self (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) : singleV F v t v = t := by
  show (Pi.single v t : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) v = t
  simp

open Classical in
theorem singleV_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (t : Fv F v) : singleV F v t w = 0 := by
  show (Pi.single v t : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) w = 0
  simp [h]

theorem ev_pow_mul_sub (v : HeightOneSpectrum (𝓞 F)) {W : Set (Fv F v)} (hW : W ∈ 𝓝 (0 : Fv F v)) :
    ∃ n : ℕ, ∀ s ∈ v.adicCompletionIntegers F, unifV v ^ n * s ∈ W := by
  have hK : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  have hP : ∀ s ∈ (v.adicCompletionIntegers F : Set (Fv F v)),
      ∀ᶠ z : Fv F v × Fv F v in 𝓝 ((0 : Fv F v), s), z.1 * z.2 ∈ W := by
    intro s _
    have hc : Continuous (fun z : Fv F v × Fv F v => z.1 * z.2) := continuous_fst.mul continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hW
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (0 : Fv F v)) (P := fun e s => e * s ∈ W) hP
  obtain ⟨n, hn⟩ := ((unifV_spec v).2.1.eventually h).exists
  exact ⟨n, hn⟩

def U0 (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    AddSubgroup (Af F) where
  carrier := {y | (∀ w, y w ∈ w.adicCompletionIntegers F) ∧
    ∀ w ∈ I, (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F}
  zero_mem' := ⟨fun w => by rw [af_zero]; exact zero_mem _, fun w _ => by rw [af_zero, mul_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_add]; exact add_mem (hy1 w) (hz1 w)
    · rw [af_add, mul_add]; exact add_mem (hy2 w hw) (hz2 w hw)
  neg_mem' := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [af_neg]; exact neg_mem (hy1 w)
    · rw [af_neg, mul_neg]; exact neg_mem (hy2 w hw)

theorem isOpen_adelic_neighbourhood (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsOpen (U0 I n : Set (Af F)) := by
  have h1 : IsOpen {y : Af F | ∀ w, y w ∈ w.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun w => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers w)
  have h2 : ∀ w ∈ I, IsOpen {y : Af F | (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} :=
    fun w _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers w).preimage
      (continuous_const.mul (RestrictedProduct.continuous_eval w))
  have e : (U0 I n : Set (Af F)) = {y : Af F | ∀ w, y w ∈ w.adicCompletionIntegers F} ∩
      ⋂ w ∈ I, {y : Af F | (unifV w ^ n w)⁻¹ * y w ∈ w.adicCompletionIntegers F} := by
    ext y
    simp [U0]
  rw [e]
  exact h1.inter (isOpen_biInter_finset h2)

theorem adele_character_trivial_open (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ (I : Finset (HeightOneSpectrum (𝓞 F))) (n : HeightOneSpectrum (𝓞 F) → ℕ),
      ∀ y ∈ U0 I n, ψ (pairA F 0 y) = 1 := by
  classical
  set U : Set (AF F) := {x | 1 / 2 < (ψ x).re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hψ.1)
  let Φ : (∀ v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) → AF F :=
    fun x => pairA F 0 (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hΦ : Continuous Φ :=
    continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous
  let x0 : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨0, zero_mem _⟩
  have hx0 : Φ x0 = 0 := by
    show pairA F 0 _ = 0
    have : (RestrictedProduct.structureMap _ _ Filter.cofinite x0 : Af F) = 0 := by
      apply RestrictedProduct.ext
      intro j
      rfl
    rw [this]
    rfl
  have hx0U : x0 ∈ Φ ⁻¹' U := by
    simp only [Set.mem_preimage, hx0, hUdef, Set.mem_setOf_eq, AddChar.map_zero_eq_one,
      Complex.one_re]
    norm_num
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 (hU.preimage hΦ) x0 hx0U
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ m : ℕ, w ∈ I → ∀ s ∈ w.adicCompletionIntegers F,
      ∃ h : unifV w ^ m * s ∈ ((w.adicCompletionIntegers F : Set (w.adicCompletion F))),
        (⟨unifV w ^ m * s, h⟩ : ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈ u w := by
    intro w
    by_cases hw : w ∈ I
    · obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 (hu w hw).1
      have h0 : (0 : Fv F w) ∈ t := by
        have := (hu w hw).2
        rw [← hte] at this
        exact this
      obtain ⟨m, hm⟩ := ev_pow_mul_sub w (ht.mem_nhds h0)
      refine ⟨m, fun _ s hs => ⟨mul_mem (pow_mem (unifV_spec w).2.2 m) hs, ?_⟩⟩
      rw [← hte]
      exact hm s hs
    · exact ⟨0, fun h => absurd h hw⟩
  choose n hn using hn
  refine ⟨I, n, ?_⟩
  have hbig : ∀ y ∈ U0 I n, 1 / 2 < (ψ (pairA F 0 y)).re := by
    intro y hy
    let x : ∀ v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
      fun w => ⟨y w, hy.1 w⟩
    have hx : x ∈ (I : Set _).pi u := by
      intro w hw
      have hne : unifV w ^ n w ≠ 0 := pow_ne_zero _ (unifV_spec w).1
      obtain ⟨h, hmem⟩ := hn w hw _ (hy.2 w hw)
      have e : (⟨unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w), h⟩ :
          ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) = x w := by
        apply Subtype.ext
        show unifV w ^ n w * ((unifV w ^ n w)⁻¹ * y w) = y w
        rw [mul_inv_cancel_left₀ hne]
      rw [← e]
      exact hmem
    have e : Φ x = pairA F 0 y := by
      show pairA F 0 _ = _
      congr 1
    have := hsub hx
    simp only [Set.mem_preimage, e, hUdef, Set.mem_setOf_eq] at this
    exact this
  intro y hy
  apply eq_one_of_pow _ (hψ.2.1 _)
  intro k
  rw [← AddChar.map_nsmul_eq_pow, ← pairA_nsmul0]
  exact hbig _ (AddSubgroup.nsmul_mem _ hy _)

def lamPsi (ψ : AddChar (AF F) ℂ) : Submodule (𝓞 F) F where
  carrier := {a | ∀ r : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((r : F) * a))) = 1}
  add_mem' := by
    intro a b ha hb r
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_add, map_add, adele_pairing_zero_add, AddChar.map_add_eq_mul, ha r, hb r, one_mul]
  zero_mem' := by
    intro r
    rw [mul_zero, map_zero]
    exact AddChar.map_zero_eq_one ψ
  smul_mem' := by
    intro c a ha r
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := ha (r * c)
    rw [Algebra.smul_def]
    convert this using 4
    push_cast
    rw [mul_assoc]

def chiInf (ψ : AddChar (AF F) ℂ) : AddChar (InfiniteAdeleRing F) ℂ where
  toFun x := ψ (pairA F x 0)
  map_zero_eq_one' := by
    show ψ (pairA F 0 0) = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' x y := by
    show ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · show x + y = x + y
      rfl
    · show (0 : Af F) = 0 + 0
      rw [add_zero]

theorem algebraMap_AF (a : F) :
    algebraMap F (AF F) a = pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a) := by
  refine Prod.ext ?_ ?_
  · show (algebraMap F (AF F) a).1 = algebraMap F (Ainf F) a + 0
    rw [add_zero]
    rfl
  · show (algebraMap F (AF F) a).2 = 0 + algebraMap F (Af F) a
    rw [zero_add]
    rfl

theorem psi_fin_of_char (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (a : F) (h : ψ (pairA F 0 (algebraMap F (Af F) a)) = 1) :
    chiInf ψ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
  have h1 := hψ.2.2.1 a
  rw [algebraMap_AF, AddChar.map_add_eq_mul, h, mul_one] at h1
  exact h1

theorem condExact_of (hS : SAf) (hC : ChInf) : CondExact := by
  intro F _ _ ψ hψ
  classical
  obtain ⟨I, n, hU⟩ := adele_character_trivial_open ψ hψ
  by_contra hne
  rw [Filter.not_eventually, Filter.frequently_cofinite_iff_infinite] at hne
  set X := {v : HeightOneSpectrum (𝓞 F) | ¬∀ t : Fv F v,
    (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F}
    with hX

  have key : ∀ v ∈ X, v ∉ I → ∃ a : F, 1 < Valued.v (algebraMap F (Fv F v) a) ∧ a ∈ lamPsi ψ := by
    intro v hvX hvI
    simp only [hX, Set.mem_setOf_eq, not_forall] at hvX
    obtain ⟨t, ht, htO⟩ := hvX
    have ht1 : 1 < Valued.v t := (HeightOneSpectrum.notMem_adicCompletionIntegers (𝓞 F) F v).1 htO
    obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) (singleV F v t)
    have hdv : (singleV F v t - algebraMap F (Af F) a) v = t - algebraMap F (Fv F v) a := by
      rw [af_sub, singleV_self]
      rfl
    have hdw : ∀ w, w ≠ v → (singleV F v t - algebraMap F (Af F) a) w = - algebraMap F (Fv F w) a := by
      intro w hw
      rw [af_sub, singleV_ne v w hw, zero_sub]
      rfl
    have hta : Valued.v (t - algebraMap F (Fv F v) a) < Valued.v t := by
      have := ha.1 v
      rw [hdv, HeightOneSpectrum.mem_adicCompletionIntegers] at this
      exact lt_of_le_of_lt this ht1
    have hav : Valued.v (algebraMap F (Fv F v) a) = Valued.v t := by
      have := Valuation.map_sub_eq_of_lt_left Valued.v hta
      rwa [sub_sub_cancel] at this
    refine ⟨a, hav ▸ ht1, ?_⟩
    intro r
    have hrint : ∀ w : HeightOneSpectrum (𝓞 F),
        algebraMap F (Fv F w) (r : F) ∈ w.adicCompletionIntegers F := by
      intro w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e : Valued.v (((r : F) : w.adicCompletion F)) = w.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (r : F)
      exact (e ▸ w.valuation_le_one r : Valued.v (((r : F) : w.adicCompletion F)) ≤ 1)
    set y : Af F := algebraMap F (Af F) ((r : F) * a) with hy
    have hyw : ∀ w, y w = algebraMap F (Fv F w) (r : F) * algebraMap F (Fv F w) a := by
      intro w
      rw [hy, map_mul]
      rfl
    have hz : y - singleV F v (y v) ∈ U0 I n := by
      refine ⟨fun w => ?_, fun w hw => ?_⟩
      · rw [af_sub]
        by_cases hwv : w = v
        · subst hwv
          rw [singleV_self, sub_self]
          exact zero_mem _
        · rw [singleV_ne v w hwv, sub_zero, hyw]
          refine mul_mem (hrint w) ?_
          have := neg_mem (ha.1 w)
          rwa [hdw w hwv, neg_neg] at this
      · have hwv : w ≠ v := fun h => hvI (h ▸ hw)
        rw [af_sub, singleV_ne v w hwv, sub_zero, hyw, mul_left_comm]
        refine mul_mem (hrint w) ?_
        have := neg_mem (ha.2 w hw)
        rwa [hdw w hwv, mul_neg, neg_neg] at this
    have hsplit : pairA F 0 y = pairA F 0 (y - singleV F v (y v)) + pairA F 0 (singleV F v (y v)) := by
      rw [← adele_pairing_zero_add, sub_add_cancel]
    show ψ (pairA F 0 y) = 1
    rw [hsplit, AddChar.map_add_eq_mul, hU _ hz, one_mul]
    show psiV F ψ v (y v) = 1
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    have hq : y v / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hyw, map_mul, hav,
        mul_div_assoc, div_self ((Valuation.ne_zero_iff _).2 ht0), mul_one]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hrint v)
    have := ht _ hq
    rwa [div_mul_cancel₀ _ ht0] at this

  have hne' : ∀ c : F, ∃ v, v ∈ X ∧ v ∉ I ∧ v ∉ HeightOneSpectrum.Support (𝓞 F) c := by
    intro c
    obtain ⟨v, hv⟩ := ((hne.diff I.finite_toSet).diff (HeightOneSpectrum.Support.finite (𝓞 F) c)).nonempty
    exact ⟨v, hv.1.1, hv.1.2, hv.2⟩
  have h0 : ∃ c : F, c ≠ 0 ∧ c ∈ lamPsi ψ := by
    obtain ⟨v, hvX, hvI, -⟩ := hne' 1
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    refine ⟨a, ?_, ha⟩
    rintro rfl
    simp at ha1
  have hb : ∀ c : F, c ≠ 0 → ¬ ∀ a ∈ lamPsi ψ, ∃ r : 𝓞 F, a = c * r := by
    intro c _ hall
    obtain ⟨v, hvX, hvI, hvc⟩ := hne' c
    obtain ⟨a, ha1, ha⟩ := key v hvX hvI
    obtain ⟨r, rfl⟩ := hall a ha
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hvc
    have hc : Valued.v (algebraMap F (Fv F v) c) ≤ 1 := by
      have e : Valued.v ((c : v.adicCompletion F)) = v.valuation F c :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c
      exact (e ▸ hvc : Valued.v ((c : v.adicCompletion F)) ≤ 1)
    have hr : Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 := by
      have e : Valued.v (((r : F) : v.adicCompletion F)) = v.valuation F (r : F) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (r : F)
      exact (e ▸ v.valuation_le_one r : Valued.v (((r : F) : v.adicCompletion F)) ≤ 1)
    rw [map_mul, map_mul] at ha1
    have : Valued.v (algebraMap F (Fv F v) c) * Valued.v (algebraMap F (Fv F v) (r : F)) ≤ 1 :=
      mul_le_one' hc hr
    exact absurd ha1 (not_lt.2 this)
  have hχc : Continuous (chiInf ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  have hΛ : ∀ a ∈ lamPsi ψ, chiInf ψ (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    apply psi_fin_of_char ψ hψ a
    have := ha 1
    simpa using this
  have hall := hC F (lamPsi ψ) h0 hb (chiInf ψ) hχc hΛ
  obtain ⟨x, hx⟩ := hψ.2.2.2
  apply hx
  obtain ⟨a, ha⟩ := hS F (U0 I n) (isOpen_adelic_neighbourhood I n) x.2
  have e : x = algebraMap F (AF F) a + pairA F (x.1 - algebraMap F (Ainf F) a) 0 +
      pairA F 0 (x.2 - algebraMap F (Af F) a) := by
    rw [algebraMap_AF]
    refine Prod.ext ?_ ?_
    · show x.1 = algebraMap F (Ainf F) a + 0 + (x.1 - algebraMap F (Ainf F) a) + 0
      abel
    · show x.2 = 0 + algebraMap F (Af F) a + 0 + (x.2 - algebraMap F (Af F) a)
      abel
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.2.1 a, hU _ ha, one_mul, mul_one]
  exact hall _

end VolAAW

end PI.VolStabW
end
end

section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabW

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ ⟨c0, hc0, hc0Λ⟩ hb g hg
  classical

  have hrat1 : ∀ x : F, ∃ q : ℚ, g (c0 * x) = q := by
    intro x
    have hn : ∀ i, ∃ n : ℤ, g (c0 * integralBasis F i) = n := fun i => by
      apply hg
      rw [integralBasis_apply, mul_comm, ← Algebra.smul_def]
      exact Λ.smul_mem _ hc0Λ
    choose n hn using hn
    refine ⟨∑ i, (integralBasis F).repr x i * n i, ?_⟩
    conv_lhs => rw [← (integralBasis F).sum_repr x]
    rw [Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_smul_comm, map_rat_smul, hn i, Rat.smul_def]
  have hrat : ∀ a : F, ∃ q : ℚ, g a = q := fun a => by
    obtain ⟨q, hq⟩ := hrat1 (a / c0)
    exact ⟨q, by rwa [mul_div_cancel₀ _ hc0] at hq⟩
  choose q hq using hrat
  let g' : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun a b => by
        have := g.map_add a b
        rw [hq, hq, hq] at this
        exact_mod_cast this
      map_smul' := fun c a => by
        have := map_rat_smul g c a
        rw [hq, hq] at this
        have h : ((q (c • a) : ℚ) : ℂ) = ((c * q a : ℚ) : ℂ) := by
          rw [this, Rat.smul_def]; norm_cast
        simp only [RingHom.id_apply, smul_eq_mul]
        exact_mod_cast h }
  have hg' : ∀ a, g a = (g' a : ℂ) := hq
  let β := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm g'
  have hβ : ∀ a, Algebra.traceForm ℚ F β a = g' a := fun a =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ F) g' a
  have hβ0 : β = 0 := by
    by_contra hβne
    obtain ⟨d, hdS, hd⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdS
    have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    apply hb (β * algebraMap (𝓞 F) F d)⁻¹ (inv_ne_zero (mul_ne_zero hβne hdF))
    intro a ha
    have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      intro h
      have hm : (1 : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
        (FractionalIdeal.mem_one_iff (𝓞 F)⁰).2 ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at hm
      exact one_ne_zero hm
    have hmem : β * a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_dual h1]
      intro b hb1
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 F)⁰).1 hb1
      have hra : algebraMap (𝓞 F) F r * a ∈ Λ := by
        rw [← Algebra.smul_def]; exact Λ.smul_mem r ha
      obtain ⟨n, hn⟩ := hg _ hra
      refine ⟨n, ?_⟩
      rw [Algebra.traceForm_apply,
        show β * a * algebraMap (𝓞 F) F r = β * (algebraMap (𝓞 F) F r * a) by ring,
        ← Algebra.traceForm_apply, hβ]
      have h1 : ((g' (algebraMap (𝓞 F) F r * a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        rw [← hg', hn]; push_cast; rfl
      have h2 : g' (algebraMap (𝓞 F) F r * a) = (n : ℚ) := by exact_mod_cast h1
      rw [h2]
      simp
    obtain ⟨r, hr⟩ := hd _ hmem
    refine ⟨r, ?_⟩
    rw [show (r : F) = algebraMap (𝓞 F) F r from rfl, hr, Algebra.smul_def]
    field_simp
  intro a
  rw [hg', ← hβ, hβ0]
  simp

theorem chInf_of_lift (hL : ChLift) : ChInf := chInf_of hL addIntF_holds

end PI.VolStabW
end
end

section
namespace PI.VolStabW

open VolAAW

theorem volAA_of_chInf (hC : ChInf) : VolAA :=
  volAA_of (condAA_of (condExact_of sAf_holds hC))

theorem volAA_of_lift (hL : ChLift) : VolAA :=
  volAA_of_chInf (chInf_of_lift hL)

end PI.VolStabW
end

section
noncomputable section

open NumberField Complex

namespace PI.VolStabW

namespace ChLiftW

theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m := by
    intro t ht
    rcases le_total (0 : ℝ) n with h | h
    · rw [Set.uIcc_of_le h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
    · rw [Set.uIcc_of_ge h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
  rw [hn]
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  rcases lt_or_gt_of_ne hn0 with h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨m, hm⟩ := key (-1 / 2) (by
      rw [Set.uIcc_of_ge (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨m, hm⟩ := key (1 / 2) (by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := fun x h => by
    have := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at this
    exact one_ne_zero this
  let f : C(W, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨χ x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, ⟨hg0, hgl⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by ext; simp [f, h0])
  have hge : ∀ x, exp (g x) = χ x := fun x => congrArg Subtype.val (congrFun hgl x)
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let D : W × W → ℂ := fun p => g (p.1 + p.2) - g p.1 - g p.2
  have hDc : Continuous D := by
    have := g.continuous
    fun_prop
  have hDint : ∀ p, ∃ n : ℤ, D p = n * (2 * Real.pi * I) := fun p => by
    rw [← Complex.exp_eq_one_iff]
    simp only [D, Complex.exp_sub, hge, hadd]
    field_simp [hne p.1, hne p.2]
  let ψ : W × W → ℝ := fun p => (D p / (2 * Real.pi * I)).re
  have hψint : ∀ p, ∃ n : ℤ, ψ p = n := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    refine ⟨n, ?_⟩
    simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]
    simp
  have hψ : ∀ p, D p = ψ p * (2 * Real.pi * I) := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    have : ψ p = n := by simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]; simp
    rw [this, hn]; push_cast; ring
  have hψc : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hψ0 : ψ (0, 0) = 0 := by simp [ψ, D, hg0]
  have hD0 : ∀ p, D p = 0 := fun p => by
    rw [hψ p, int_valued_zero ψ hψc hψint (0, 0) hψ0 p]; simp
  refine ⟨{ toFun := g, map_zero' := hg0, map_add' := fun x y => ?_ }, g.continuous,
    fun x => (hge x).symm⟩
  have := hD0 (x, y)
  simp only [D] at this
  linear_combination this

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  by_cases hv : v.IsReal
  · exact lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    exact lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x :=
  Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add, Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabW
end
end

section
namespace PI.VolStabW

theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabW
end
