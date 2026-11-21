import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

section
noncomputable section

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.CharFin
open scoped TensorProduct nonZeroDivisors

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem unit_pow_card_cong (N : ℕ) (hN : 0 < N) (v : (hatRing F E)ˣ) :
    ∃ w : hatRing F E, (v : hatRing F E) ^ Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ - 1 = N * w := by
  have dec : ∀ x : hatRing F E, ∃ a : 𝓞 E, ∃ w : hatRing F E, x = diagInt F E a + (N : hatRing F E) * w := by
    intro x
    obtain ⟨a, w, hw, e⟩ := exists_int_add_nsmul F E N hN x x.2
    refine ⟨a, ⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [e, nsmul_eq_mul]; simp; rfl
  obtain ⟨a, w, ea⟩ := dec v
  obtain ⟨b, w', eb⟩ := dec (v⁻¹ : (hatRing F E)ˣ)
  have hv : (v : hatRing F E) * (v⁻¹ : (hatRing F E)ˣ) = 1 := Units.mul_inv v
  let z : hatRing F E := -(diagInt F E a * w' + w * diagInt F E b + N * w * w')
  have h1 : diagInt F E (a * b - 1) = N * z := by
    rw [ea, eb] at hv
    rw [map_sub, map_mul, map_one]
    simp only [z]
    linear_combination hv
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : diag F E (((a * b - 1 : 𝓞 E) : E) / N) = z := by
    apply (isUnit_nat F E hN).mul_left_cancel
    rw [← map_natCast (diag F E), ← map_mul, mul_div_cancel₀ _ hN', map_natCast]
    have := congrArg (hatRing F E).subtype h1
    rw [map_mul, map_natCast] at this
    exact this
  obtain ⟨r, hr⟩ := GlobalTheory.AdIdem.mem_range_of_one_tmul_mem F E (x := ((a * b - 1 : 𝓞 E) : E) / N)
    (by rw [← diag_apply, h2]; exact z.2)
  have h3 : a * b - 1 = N * r := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_natCast, hr, mul_div_cancel₀ _ hN']
  let q := Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)})
  have h4 : q a * q b = 1 := by
    rw [← map_mul, ← map_one q, Ideal.Quotient.eq, h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ with hk
  have h5 : (Units.mkOfMulEqOne _ _ h4) ^ k = 1 := pow_card_eq_one'
  have h6 : q (a ^ k) = q 1 := by
    rw [map_pow, map_one]
    exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val h5)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h6)
  have h7 := congrArg (diagInt F E) hc
  rw [map_sub, map_pow, map_one, map_mul, map_natCast] at h7
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (v : hatRing F E) (diagInt F E a) k
  refine ⟨w * d + diagInt F E c, ?_⟩
  linear_combination hd + h7 + d * ea

variable (c : E ≃ₐ[F] E)

theorem pow_mem_ratOne_sup_congOne (hc : ∀ y, c (c y) = y) (N : ℕ) (hN : 0 < N) (x : (RA F E)ˣ)
    (hx : (x : RA F E) * bar c x = 1) :
    x ^ (2 * classNumber E * Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ) ∈ ratOne c ⊔ congOne c N := by
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ with hk
  obtain ⟨b, hb, s, t, e, hst⟩ := pow_classNumber F E x
  have hst' : (s : RA F E) * t = 1 := congrArg Subtype.val hst
  have hbst : bar c s * bar c t = 1 := by rw [← map_mul, hst', map_one]
  have hcb : c b ≠ 0 := by simpa using hb
  have hq : b / c b ≠ 0 := div_ne_zero hb hcb
  let r : (RA F E)ˣ := (isUnit_diag F E hq).unit
  have hr : r ∈ ratOne c := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    change diag F E (b / c b) * diag F E (c (b / c b)) = 1
    rw [← map_mul, map_div₀, hc, div_mul_div_comm, mul_comm b, div_self (mul_ne_zero hcb hb), map_one]
  let v : (hatRing F E)ˣ := Units.mkOfMulEqOne (s * ⟨_, bar_mem c t.2⟩) (t * ⟨_, bar_mem c s.2⟩)
    (Subtype.ext (by
      change (s : RA F E) * bar c t * (t * bar c s) = 1
      linear_combination (bar c s * bar c t) * hst' + hbst))
  let u : (RA F E)ˣ := Units.map (hatRing F E).subtype.toMonoidHom v
  have hu : (u : RA F E) = s * bar c t := rfl
  have hun : (u : RA F E) * bar c u = 1 := by
    rw [hu, map_mul, bar_bar c hc]
    linear_combination (bar c s * bar c t) * hst' + hbst
  have hx2 : x ^ (classNumber E * 2) = r * u := by
    apply Units.ext
    have h1 : (x : RA F E) ^ classNumber E * bar c ((x : RA F E) ^ classNumber E) = 1 := by
      rw [map_pow, ← mul_pow, hx, one_pow]
    have h2 : diag F E (b / c b) * diag F E (c b) = diag F E b := by
      rw [← map_mul, div_mul_cancel₀ _ hcb]
    have h3 : bar c (diag F E b) = diag F E (c b) := rfl
    rw [e, map_mul, h3] at h1
    rw [Units.val_pow_eq_pow_val, pow_mul, e, Units.val_mul, hu]
    change _ = diag F E (b / c b) * _
    linear_combination (diag F E (b / c b) * s * bar c t) * h1 - (diag F E b * s * s) * h2
      - (diag F E (b / c b) * diag F E (c b) * diag F E b * s * s) * hbst
  have huk : u ^ k ∈ congOne c N := by
    refine ⟨?_, by rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hun, one_pow]⟩
    obtain ⟨w, hw⟩ := unit_pow_card_cong N hN v
    refine ⟨w, w.2, ?_⟩
    have := congrArg (hatRing F E).subtype hw
    rwa [map_sub, map_one, map_mul, map_natCast, map_pow] at this
  rw [mul_comm 2, pow_mul, hx2, mul_pow]
  exact Subgroup.mul_mem_sup (pow_mem hr k) huk

end GlobalTheory.NormOneChar

namespace GlobalTheory.NormOneChar

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.FinalJoin
open scoped TensorProduct

theorem tame_pow_eq_one : ∀ (D : D7) (N : ℕ) (xi : (AfE D)ˣ →* ℂˣ), 0 < N → (∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → NormOne x → xi x = 1) → (∀ x, NormOne x → CongOne N x → xi x = 1) → ∀ x, NormOne x → xi x ^ (2 * classNumber D.host.E * Nat.card (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)})ˣ) = 1 := by
  intro D N xi hN h1 h2 x hx
  have hc : ∀ (φ : D.host.E →+* ℂ) (y : D.host.E), φ (GlobalTheory.Member.cF D y) = starRingEnd ℂ (φ y) :=
    fun φ y => @IsCMField.complexEmbedding_complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ φ y
  have hcc : ∀ y, GlobalTheory.Member.cF D (GlobalTheory.Member.cF D y) = y := fun y =>
    D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])
  have hcong : ∀ (x : (AfE D)ˣ), x ∈ congOne (GlobalTheory.Member.cF D) N ↔ CongOne N x ∧ NormOne x := by
    intro x
    unfold CongOne
    simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
    exact Iff.rfl
  obtain ⟨r, ⟨⟨a, ha⟩, hr⟩, k, hk, e⟩ :=
    Subgroup.mem_sup.1 (pow_mem_ratOne_sup_congOne (GlobalTheory.Member.cF D) hcc N hN x hx)
  rw [← map_pow]
  have e' : xi (r * k) = 1 := by
    rw [map_mul, h1 r a ha hr, h2 k ((hcong k).1 hk).2 ((hcong k).1 hk).1, mul_one]
  rw [← e']
  exact congrArg xi e.symm

end GlobalTheory.NormOneChar
end
end

section
noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem exists_xiOK_of_root (D : D7) (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (h : Complex.exp (2 * Real.pi * Complex.I / (xiOrd D.host (D.host.g 0 * D.host.g 1 * p) : ℕ)) ∈ FO D) :
    ∃ xi, XiOK D p xi := by
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime.pos, D.host.pde'_prime.pos]
  have hN : 0 < D.host.g 0 * D.host.g 1 * p :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp0
  obtain ⟨xi, m, hm, a1, a2, a3, a4, -⟩ := GlobalTheory.NormOneChar.exists_xi D p hp
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have : Finite (𝓞 D.host.E ⧸ Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have ho : 0 < xiOrd D.host (D.host.g 0 * D.host.g 1 * p) :=
    Nat.mul_pos (Nat.mul_pos two_pos (classNumber_pos _)) Nat.card_pos
  refine ⟨xi, a1, a2, a3, ⟨m, hm, a4⟩, fun x hn => GlobalTheory.NormOneChar.mem_of_pow_eq_one ho h ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (GlobalTheory.NormOneChar.tame_pow_eq_one D _ xi hN a1 a2 x hn)

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩

set_option maxHeartbeats 4000000 in

theorem jointQ_of_small_field : ∀ (X : Stages) (F : IntermediateField ℚ ℂ), Rich X.B.toPre F → (∀ L : ℝ, HostSz X.B.host L → Sz F (poR X.B.R L) (poR X.B.R L)) → (∀ z, z ∈ F ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z) → JointQ X.toD7 := by
  intro X F hR hS hF
  obtain rfl : F = FO X.toD7 := SetLike.ext fun z => (hF z).trans (mem_FO_assembled_iff X z).symm
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hp0 : 0 < p := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_prime.pos, X.B.host.pde'_prime.pos]
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rcases hp with rfl | rfl
      exacts [hR.roots _ (by simp), hR.roots _ (by simp)]
    · exact curveOver_of_weberSet X.toD7 _
        (Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0) (hR.host _)
        fun L hL => hR.weber L hL p (by simpa using hp)
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), exists_xiOK_of_root _ _ (Or.inl rfl) ?_,
    exists_xiOK_of_root _ _ (Or.inr rfl) ?_, hS⟩
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde)) (by simp)
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde')) (by simp)

end GlobalTheory.FieldSize
end
end
