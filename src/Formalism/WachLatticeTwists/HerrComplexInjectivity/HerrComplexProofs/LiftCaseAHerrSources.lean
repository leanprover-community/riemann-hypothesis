import Formalism.WachLatticeTwists.HerrComplexInjectivity.LiftCaseAHerrSources
import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneInvariants
import Formalism.WachLatticeTwists.HerrComplexInjectivity.ExtInputNA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatementA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.ShortExactSequenceHolds
import Formalism.WachLatticeTwists.HerrComplexInjectivity.StatInvWach
import Formalism.WachLatticeTwists.WachProductBases.WachConsequencesFurther
import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneStatedForm

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem semilinear_case_a : StatSemiA := by
  intro ℓ _ A R _ _ _ _ B M D P _ _ _ _ _ _ _ _ W dd u c jumps ρ κ _ t γR locA loc γl n a hGQ hdd
    hγt hmod hbij hγls hlocs hlocγ hQt hXu hc hP4 hP4e hP5 hj d hd
  choose hXunit r₀ hr₀ using hXu
  choose πi hπi using fun x => (hXunit x).exists_left_inv
  let dl : ρ → P →ₗ[ℤ_[ℓ]] P := fun x =>
    (DistribSMul.toLinearMap ℤ_[ℓ] P (πi x)).comp (γl x - LinearMap.id)
  have hdl : ∀ x v, dl x v = πi x • (γl x v - v) := fun _ _ => rfl
  have hdl' : ∀ x v, locA x B.X • dl x v = γl x v - v := by
    intro x v
    rw [hdl, smul_smul, mul_comm, hπi, one_smul]
  have hddNQ : ∀ d, (∃ k : ℕ, B.Q ^ k • d ∈ W.N) → ∃ k : ℕ, B.Q ^ k • dd d ∈ W.N := by
    rintro d ⟨k, hk⟩
    obtain ⟨x', hx', h⟩ := affineLine_localAcyclicity_of_strictHenselian_points ℤ_[ℓ] A B M D W k hGQ d hk
    refine ⟨k, ?_⟩
    have : dd d = x' := by
      have h0 : B.X • (dd d - x') = 0 := by rw [smul_sub, hdd, h, sub_self]
      exact sub_eq_zero.1 (W.X_inj _ h0)
    rw [this]
    exact hx'
  have hlocd : ∀ x v, (∃ k : ℕ, B.Q ^ k • v ∈ W.N) → loc x (dd v) = dl x (loc x v) := by
    intro x v hv
    rw [hdl, ← hlocγ x v hv, ← map_sub, ← hdd, hlocs x _ _ (hddNQ v hv), smul_smul, hπi, one_smul]
  have hc' : ∀ b : ℤ, -(ℓ : ℤ_[ℓ]) * c b = ((u ^ (-b) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro b
    linear_combination (-1 : ℤ_[ℓ]) * hc b
  let Ll : ρ → Submodule ℤ_[ℓ] P :=
    fun x => (Submodule.span R (Set.range (n x))).restrictScalars ℤ_[ℓ]
  let Ly : ρ → Submodule ℤ_[ℓ] P := fun x =>
    ((Submodule.span R (Set.range (n x))).comap
      (t ^ M • (LinearMap.id : P →ₗ[R] P))).restrictScalars ℤ_[ℓ]
  refine consequence_two_global ℤ_[ℓ] A D W.N dd B.Q M _ ρ (fun _ => P) loc dl Ll Ly hlocd hP5 hddNQ ?_ ?_ d hd
  · intro d hd x
    obtain ⟨v, hv, hQ⟩ := hQt x
    obtain ⟨vi, hvi⟩ := hv.exists_left_inv
    show t ^ M • loc x d ∈ Submodule.span R (Set.range (n x))
    have h1 := hP4 x _ hd
    rw [hlocs x _ d ⟨M, hd⟩, map_pow, hQ, mul_pow, mul_smul] at h1
    have h2 : t ^ M • loc x d = vi ^ M • (v ^ M • t ^ M • loc x d) := by
      rw [smul_smul, ← mul_pow, hvi, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  · intro x v hv
    exact consequence_four_local ℤ_[ℓ] R P t (locA x B.X) (r₀ x) u (-(ℓ : ℤ_[ℓ])) γR (γl x) (dl x) κ (n x) (a x)
      c M (eigSet jumps M) hγt (hγls x) hmod hbij (hXunit x) (hr₀ x) (hdl' x) hc' (hP4e x)
      (fun k j hj' => Finset.mem_image.2 ⟨(a x k, j), Finset.mem_product.2 ⟨hj x k, hj'⟩, rfl⟩) v hv

theorem base_case_a : StatBaseA := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB hs hΔ hmod hcap hreg
  obtain ⟨hφ, hγ, hw, ⟨r, hr, hQ⟩, ε₀, hε₀, hjX⟩ := hΔ
  choose w hwu hw using hw
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  obtain ⟨-, -, -, ⟨t, ht⟩, -, -⟩ := base_facts_holds O A S
  rw [hX] at ht
  have hφπ : S.φ S.π = S.π * S.Q := by have := S.φ_X; rwa [hX] at this
  have hinvQ : ∀ d : Δ, d • IB.j B.Q = IB.j B.Q := (IB.j_range _).2 ⟨_, rfl⟩
  have hinvX : ∀ d : Δ, d • IB.j B.X = IB.j B.X := (IB.j_range _).2 ⟨_, rfl⟩
  have hinvu : ∀ d : Δ, d • algebraMap O A S.u = algebraMap O A S.u :=
    (IB.j_range _).2 ⟨algebraMap O A₀ S.u, IB.j.commutes _⟩
  obtain ⟨-, -, ⟨v, hv, hvinv, hφ'⟩, ⟨t', hγ'⟩⟩ := invariant_norm_holds A Δ (S.φ : A →+* A) (S.γ : A →+* A)
    S.π S.Q r (IB.j B.Q) (algebraMap O A S.u) t w hφ hγ hφπ hwu hw hr hQ hinvQ ht hinvu
  obtain ⟨ε₁, hε₁⟩ := hε₀.exists_right_inv
  have hjε : IB.j ε₀ * IB.j ε₁ = 1 := by rw [← map_mul, hε₁, map_one]
  set Nm : A := ∏ d : Δ, d • S.π with hNm
  have hNX : Nm = IB.j ε₁ * IB.j B.X := by
    rw [hjX]; linear_combination (-Nm) * hjε
  have hφ'' : S.φ Nm = v * Nm * IB.j B.Q ^ Fintype.card Δ := hφ'
  have hγ'' : S.γ Nm = Nm * (algebraMap O A S.u ^ Fintype.card Δ + S.π * t') := hγ'
  obtain ⟨t₁, ht₁⟩ := hmod (IB.j ε₀)
  have ht₁' : S.γ (IB.j ε₀) = IB.j ε₀ + S.π * t₁ := by
    have h0 : S.γ (IB.j ε₀) - IB.j ε₀ = S.X * t₁ := ht₁
    rw [hX] at h0
    linear_combination h0
  constructor
  · obtain ⟨v₀, hv₀⟩ := (IB.j_range v).1 hvinv
    refine ⟨B.φ ε₀ * v₀ * ε₁, IB.j_inj ?_⟩
    rw [IB.j_φ, map_mul, map_mul, map_pow, map_mul, map_mul, hv₀, IB.j_φ]
    conv_lhs => rw [hjX]
    rw [map_mul, hφ'', hNX]
    ring
  · have hγX : ∃ z : A, S.γ (IB.j B.X) =
        IB.j B.X * (algebraMap O A S.u ^ Fintype.card Δ + S.π * z) := by
      refine ⟨(IB.j ε₀ * t' + t₁ * algebraMap O A S.u ^ Fintype.card Δ + t₁ * S.π * t') * IB.j ε₁, ?_⟩
      conv_lhs => rw [hjX]
      rw [map_mul, hγ'', ht₁']
      conv_rhs => rw [hjX]
      linear_combination (-(Nm * S.π * (IB.j ε₀ * t' + t₁ * algebraMap O A S.u ^ Fintype.card Δ
        + t₁ * S.π * t'))) * hjε
    obtain ⟨z, hz⟩ := hγX
    have hinv : ∀ d : Δ, d • (S.π * z) = S.π * z := by
      intro d
      apply sub_eq_zero.1
      apply hreg
      have e1 : d • (S.γ (IB.j B.X)) = S.γ (IB.j B.X) := by rw [← hγ, hinvX d]
      rw [hz, smul_mul', smul_add, smul_pow', hinvu, hinvX d] at e1
      linear_combination e1
    obtain ⟨a', ha', hpa⟩ := hcap z hinv
    obtain ⟨t₀, ht₀⟩ := (IB.j_range a').1 ha'
    refine ⟨t₀, IB.j_inj ?_⟩
    rw [IB.j_γ, map_mul, map_add, map_mul, ht₀, IB.j.commutes, map_pow, hz, hpa]

theorem gamma_quotient_case_a : StatGammaQA := by
  intro O A₀ _ _ _ B hQ hw hrad
  obtain ⟨w, hw⟩ := hw
  have hQ' : B.Q = B.X + (B.p : A₀) := hQ
  refine ⟨1 + B.X * w, ?_, ⟨w, rfl⟩, ?_⟩
  · have := Ideal.mem_jacobson_bot.1 hrad w
    rwa [add_comm] at this
  · have h2 : B.γ B.X = B.X + B.X * B.Q * w := by linear_combination hw
    have h3 : B.γ B.Q = B.γ B.X + (B.p : A₀) := by
      conv_lhs => rw [hQ']
      rw [map_add, map_natCast]
    rw [h3, h2]
    linear_combination (-1 : A₀) * hQ'

theorem ceiling_bound_holds : StatCeil := by
  intro ℓ H hℓ
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2, one_mul]
  have hpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hpos]
    have h1 := Nat.div_add_mod (H + m) (m + 1)
    have h2 : (H + m) % (m + 1) < m + 1 := Nat.mod_lt (H + m) (Nat.succ_pos m)
    have h3 : H ≤ (H + m) / (m + 1) * (m + 1) := by
      rw [mul_comm]; omega
    exact_mod_cast h3
  · have h1 := Nat.le_ceil ((H : ℚ) / ((m + 1 : ℕ) : ℚ))
    rw [div_le_iff₀ hpos] at h1
    have h2 : H ≤ ⌈(H : ℚ) / ((m + 1 : ℕ) : ℚ)⌉₊ * (m + 1) := by exact_mod_cast h1
    have hm1 : 0 < m + 1 := Nat.succ_pos m
    refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hm1).2 ?_)
    rw [Nat.succ_mul]
    omega

theorem x_kills_case_a : StatXKillsA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₁ ρ₂ D₁' D₂' _ _ _ _ _ _ _ _ V₁ V₂ F J₁ J₂ hℓ hs hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH
    hcard hΔ hρN hρf hρs hF n hn
  obtain ⟨-, -, hinv, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H H hR hD a0 a1 a2 b0 b1
    b2 c0 c1 c2 hP6 hM (fun i => by have := hH i; omega) hH
  obtain ⟨-, -, hw, -, ε₀, -, hjX⟩ := hΔ
  choose w hwu hw using hw
  have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hπ' : IB.j B.X = (IB.j ε₀ * ∏ d : Δ, w d) * S.π ^ (ℓ - 1) := by
    rw [hjX, mul_assoc, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun d _ => hw d
  have hunit : IsUnit ((Fintype.card Δ : ℕ) : ℤ_[ℓ]) := by
    rw [hcard, Nat.cast_sub (by omega), Nat.cast_one]
    have h0 : IsUnit (1 - (ℓ : ℤ_[ℓ])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.prime_p.not_isUnit
    have : (ℓ : ℤ_[ℓ]) - 1 = -(1 - (ℓ : ℤ_[ℓ])) := by ring
    rw [this]
    exact h0.neg
  have hXinv : ∀ d : Δ, d • IB.j B.X = IB.j B.X := (IB.j_range _).2 ⟨_, rfl⟩
  have key := hinv (IB.j B.X) (IB.j ε₀ * ∏ d : Δ, w d) 1 (ℓ - 1) Δ ρ₁ ρ₂ hs (by rw [hℓ, one_mul]) hπ' hunit hρN
    hρf (fun i d x => by rw [hρs, hXinv])
  rw [hℓ, ceiling_bound_holds ℓ H h2] at key
  have hy : ∀ i d, ρ₂ i d (J₂.j n i) = J₂.j n i := (J₂.j_range _).2 ⟨n, rfl⟩
  choose n₁ hn₁ hn₁inv hn₁f using fun i => key i (J₂.j n i) ((J₂.j_N n).1 hn i) (hy i)
  obtain ⟨m, hm⟩ := (J₁.j_range n₁).1 hn₁inv
  refine ⟨m, (J₁.j_N m).2 (fun i => by rw [hm]; exact hn₁ i), J₂.j_inj ?_⟩
  funext i
  rw [hF, hm, hn₁f, J₂.j_smul, map_pow]

theorem regulator_quotient_case_a : StatRegLQA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ M₀ D' _ _ _ _ V J hℓ hL
  obtain ⟨-, -, hsat, -⟩ := hL
  have hl : ∀ d : D, (ℓ : ℤ_[ℓ]) • d = (S.ℓ : A) • d := by
    intro d; rw [hℓ, ← algebraMap_smul A (ℓ : ℤ_[ℓ]) d, map_natCast]
  refine ⟨?_, ?_⟩
  · rintro n hn ⟨m, hm, h⟩
    obtain ⟨m', hm'⟩ := V.Q_bij.2 m
    have hm'' : B.Q • m' = m := hm'
    have hn' : n = (ℓ : ℤ_[ℓ]) • m' := by
      apply V.Q_bij.1
      show B.Q • n = B.Q • ((ℓ : ℤ_[ℓ]) • m')
      rw [smul_comm, hm'', h]
    refine ⟨m', (J.j_N _).2 fun i => hsat i _ ?_, hn'⟩
    have h1 := (J.j_N n).1 hn i
    rw [hn', map_smul, Pi.smul_apply, hl] at h1
    exact h1
  · intro h x hx
    apply J.j_inj
    rw [map_zero]
    funext i
    apply h
    rw [← Pi.smul_apply, ← map_smul, hx, map_zero]
    rfl

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem extension_case_a : StatExtA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D _ _ _ _ W M₀ D' _ _ _ _ V Hh _ _ cl Hf M h H hℓ hs hR
    hD hP2 hP5 hL hM hH hcard hΔ hE κ hκ
  obtain ⟨X, Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, Jp, Jt, p2p, p2t, p5p, p5t,
    lp, lt, p6, -, -, ⟨d1, d2, d3⟩, hF, hdict⟩ := hE κ hκ
  exact ⟨X, x_kills_case_a ℓ A A₀ S B Δ IB ι pr D Dp Dt W Wp Wt E M h M₀ H ρp ρt X.Dp X.Dt X.Wp X.Wt
    X.S.π Jp Jt hℓ hs hR hD hP2 p2p p2t hP5 p5p p5t hL lp lt p6 hM hH hcard hΔ d1 d2 d3 hF, hdict⟩

theorem composition_case_a : StatCompA := by
  intro ℓ _ hℓ2 A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ V₀ V₁ V₂ Sq J₀ J₁ J₂ u jumps δ R P ρ κ _ _ _ _ _ _ _ L
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g _ hℓ hs hc hu hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard
    hΔ hmodπ hcap hreg hQL hdiv hjac _ _ _ hΔM hF hδ hnt hP4 hj hnat hc1 hc2 hinj he1 he2 hrat
  obtain ⟨-, -, -, -, -, -, -, q8, -, -⟩ := base_case_b ℓ A S hℓ
  have hval : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 := by rw [hu, q8 hc, hs]
  obtain ⟨hPhi, hGX⟩ := base_case_a ℤ_[ℓ] A A₀ S B Δ IB hs hΔ hmodπ hcap hreg
  rw [hcard] at hPhi hGX
  rw [← hu] at hGX
  have hGQ := gamma_quotient_case_a ℤ_[ℓ] A₀ B hQL hdiv hjac
  obtain ⟨c, hcc, -, -⟩ := consequence_five_holds ℓ u hℓ2 hval
  obtain ⟨l1, l3⟩ := regulator_quotient_case_a ℓ A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ M₀ D₀' V₀ J₀ hℓ c0
  obtain ⟨d1, d2, d3⟩ := hΔM
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hP4
  have hQI : B.Q ∈ Ideal.span {(ℓ : A₀), B.X} := by
    have hQ' : B.Q = B.X + (B.p : A₀) := hQL
    rw [hQ', hp]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hφI : ∀ a ∈ Ideal.span {(ℓ : A₀), B.X}, B.φ a ∈ Ideal.span {(ℓ : A₀), B.X} := by
    intro a ha
    have : Ideal.span {(ℓ : A₀), B.X} ≤ (Ideal.span {(ℓ : A₀), B.X}).comap (B.φ : A₀ →+* A₀) := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · show (B.φ : A₀ →+* A₀) (ℓ : A₀) ∈ Ideal.span {(ℓ : A₀), B.X}
        rw [map_natCast]
        exact Ideal.subset_span (by simp)
      · show B.φ B.X ∈ Ideal.span {(ℓ : A₀), B.X}
        obtain ⟨v, hv⟩ := B.φX
        rw [hv]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    exact this ha
  exact lift_exists_first_case ℓ hℓ2 A₀ B M₀ u H jumps c hp hPhi hGX hval hcc D₀' D₁' D₂' V₀ V₁ V₂ Sq δ H₁ H₂ cl₁
    cl₂ Hf₁ Hf₂ g (Ideal.span {(ℓ : A₀), B.X}) hδ hQI hφI l1 (l3 hnt)
    (x_kills_case_a ℓ A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₁ ρ₂ D₁' D₂' V₁ V₂ Sq.π J₁ J₂ hℓ
      hs hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hcard hΔ d1 d2 d3 hF)
    (semilinear_case_a ℓ A₀ R B M₀ D₀' P V₀ δ u c jumps ρ κ L.t L.γR L.locA L.loc L.γl L.n L.a hGQ hδ p1 p2
      p3 p4 p5 p6 p7 p8 hcc p9 p10 p11 hj)
    hnat hc1 hc2 hinj
    (extension_case_a ℓ A A₀ S B Δ IB ι pr D₁ W₁ M₀ D₁' V₁ H₁ cl₁ Hf₁ M h H hℓ hs hR hD a1 b1 c1 hM hH hcard
      hΔ he1)
    (extension_case_a ℓ A A₀ S B Δ IB ι pr D₂ W₂ M₀ D₂' V₂ H₂ cl₂ Hf₂ M h H hℓ hs hR hD a2 b2 c2 hM hH hcard
      hΔ he2) hrat

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem wach_invariants_holds : StatInvWach := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ M h M₀ D' _ _ _ _ j φ' γ' hs hΔ hGQ hP5 hM
    hinj hsm hrange hφ hγ hρ hP9
  obtain ⟨-, -, hw, ⟨r, hr, hQ⟩, ε₀, hε₀, hjX⟩ := hΔ
  choose w hwu hw using hw
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  obtain ⟨r', hr'⟩ := hr.exists_left_inv
  have hjQ : IB.j B.Q = r' * S.Q := by rw [hQ, ← mul_assoc, hr', one_mul]
  have hQinj : ∀ y : D, IB.j B.Q • y = 0 → y = 0 := by
    intro y hy
    apply W.Q_bij.1
    show S.Q • y = S.Q • (0 : D)
    rw [hQ, mul_smul, hy, smul_zero, smul_zero]
  have hinvQ : ∀ d : Δ, d • IB.j B.Q = IB.j B.Q := (IB.j_range _).2 ⟨_, rfl⟩
  let p : A → Prop := fun a => ∀ y : D, a • y = 0 → y = 0
  have pmul : ∀ a b, p a → p b → p (a * b) :=
    fun a b ha hb y hy => hb y (ha _ (by rwa [smul_smul]))
  have punit : ∀ a, IsUnit a → p a := by
    intro a ha y hy
    obtain ⟨a', ha'⟩ := ha.exists_left_inv
    rw [← one_smul A y, ← ha', mul_smul, hy, smul_zero]
  have pπ : p S.π := fun y hy =>
    W.X_bij.1 (show S.X • y = S.X • (0 : D) by rw [hX, hy, smul_zero])
  have pX : p (IB.j B.X) := by
    rw [hjX]
    refine pmul _ _ (punit _ (hε₀.map IB.j))
      (Finset.prod_induction _ p pmul (punit 1 isUnit_one) fun d _ => ?_)
    rw [hw d]
    exact pmul _ _ (punit _ (hwu d)) pπ
  let N : Submodule A₀ D' :=
    { carrier := {x | ∀ i, j x i ∈ W.N i}
      add_mem' := by
        intro a b ha hb i
        rw [map_add]
        exact (W.N i).add_mem (ha i) (hb i)
      zero_mem' := by
        intro i
        rw [map_zero]
        exact (W.N i).zero_mem
      smul_mem' := by
        intro a x hx i
        rw [hsm]
        exact (W.N i).smul_mem _ (hx i) }
  have hQbij : Function.Bijective (fun x : D' => B.Q • x) := by
    constructor
    · intro x y hxy
      have hxy' : B.Q • x = B.Q • y := hxy
      apply hinj
      funext i
      have h1 : j (B.Q • x) i = j (B.Q • y) i := by rw [hxy']
      rw [hsm, hsm] at h1
      exact sub_eq_zero.1 (hQinj _ (by rw [smul_sub, h1, sub_self]))
    · intro x
      choose y hy using fun i => W.Q_bij.2 (r • j x i)
      have hy' : ∀ i, IB.j B.Q • y i = j x i := by
        intro i
        have h1 : S.Q • y i = r • j x i := hy i
        rw [hjQ, mul_smul, h1, smul_smul, hr', one_smul]
      have hxinv : ∀ i d, ρ i d (j x i) = j x i := (hrange _).2 ⟨x, rfl⟩
      have hyinv : ∀ i d, ρ i d (y i) = y i := by
        intro i d
        apply sub_eq_zero.1
        apply hQinj
        have h2 : IB.j B.Q • ρ i d (y i) = ρ i d (IB.j B.Q • y i) := by rw [hρ, hinvQ]
        rw [smul_sub, h2, hy' i, hxinv, sub_self]
      obtain ⟨x', hx'⟩ := (hrange y).1 hyinv
      refine ⟨x', hinj (funext fun i => ?_)⟩
      show j (B.Q • x') i = j x i
      rw [hsm, hx', hy']
  have hγN : ∀ x ∈ N, ∃ x' ∈ N, γ' x - x = B.X • x' := by
    intro x hx
    obtain ⟨y, hyN, hyinv, hy⟩ := hP9 (j x) hx ((hrange _).2 ⟨x, rfl⟩)
    obtain ⟨x', hx'⟩ := (hrange y).1 hyinv
    refine ⟨x', fun i => by rw [hx']; exact hyN i, hinj (funext fun i => ?_)⟩
    rw [map_sub, Pi.sub_apply, hγ, hsm, hx', hy]
  have hγs : ∀ (a : A₀) (x : D'), γ' (a • x) = B.γ a • γ' x := by
    intro a x
    apply hinj
    funext i
    rw [hγ, hsm, W.γ_smul, hsm, IB.j_γ, hγ]
  have hφs : ∀ (a : A₀) (x : D'), φ' (a • x) = B.φ a • φ' x := by
    intro a x
    apply hinj
    funext i
    rw [hφ, hsm, W.φ_smul, hsm, IB.j_φ, hφ]
  have hcomm : ∀ x, φ' (γ' x) = γ' (φ' x) := by
    intro x
    apply hinj
    funext i
    rw [hφ, hγ, hγ, hφ, W.comm]
  have hXinj : ∀ x : D', B.X • x = 0 → x = 0 := by
    intro x hx
    apply hinj
    funext i
    rw [map_zero]
    exact pX _ (by rw [← hsm, hx, map_zero]; rfl)
  have hφN : ∀ x ∈ N, B.Q ^ M₀ • φ' x ∈ N := by
    intro x hx i
    rw [hsm, map_pow, hφ, hjQ, mul_pow, mul_smul]
    refine (W.N i).smul_mem _ ?_
    have e : S.Q ^ M₀ = S.Q ^ (M₀ - M i) * S.Q ^ M i := by
      rw [← pow_add, Nat.sub_add_cancel (hM i)]
    rw [e, mul_smul]
    exact (W.N i).smul_mem _ (hP5.1 i _ (hx (pr i)))
  have hγQN := gammaStableOfGammaQUnit_holds O A₀ B M₀ D' N γ' hGQ hQbij hγs hγN
  exact ⟨⟨N, φ', γ', hφs, hγs, hcomm, hXinj, hQbij, hφN, hγN, hγQN⟩,
    ⟨j, hinj, hsm, hrange, fun x => Iff.rfl⟩, rfl, rfl, rfl⟩

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem inv_hom {O A A₀ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing A₀]
    [Algebra O A₀] {S : HidaSetting O A} {B : Base O A₀} {Δ : Type} [Group Δ] [Fintype Δ]
    [MulSemiringAction Δ A] {IB : InvBase S B Δ} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂)
    {ρ₁ : ι → Δ →* Module.End O D₁} {ρ₂ : ι → Δ →* Module.End O D₂} {M₀ : ℕ} {D₁' D₂' : Type}
    [AddCommGroup D₁'] [Module A₀ D₁'] [Module O D₁'] [IsScalarTower O A₀ D₁']
    [AddCommGroup D₂'] [Module A₀ D₂'] [Module O D₂'] [IsScalarTower O A₀ D₂']
    {V₁ : WachMod B M₀ D₁'} {V₂ : WachMod B M₀ D₂'}
    (J₁ : InvMod IB W₁ ρ₁ V₁) (J₂ : InvMod IB W₂ ρ₂ V₂) (c₁ : J₁.Compat) (c₂ : J₂.Compat)
    (hF : ∀ i d x, F.f i (ρ₁ i d x) = ρ₂ i d (F.f i x)) :
    ∃ G : Hom V₁ V₂, ∀ x i, J₂.j (G.f x) i = F.f i (J₁.j x i) := by
  have hex : ∀ x, ∃ x', J₂.j x' = fun i => F.f i (J₁.j x i) := fun x =>
    (J₂.j_range _).1 (fun i d => by rw [← hF, (J₁.j_range _).2 ⟨x, rfl⟩ i d])
  choose f hf using hex
  have hf' : ∀ x i, J₂.j (f x) i = F.f i (J₁.j x i) := fun x i => congrFun (hf x) i
  refine ⟨{ f := { toFun := f
                   map_add' := ?_
                   map_smul' := ?_ }
            φ_comm := ?_
            γ_comm := ?_
            N_le := ?_ }, hf'⟩
  · intro a b
    apply J₂.j_inj
    funext i
    rw [map_add, Pi.add_apply, hf', hf', hf', map_add, Pi.add_apply, map_add]
  · intro a x
    apply J₂.j_inj
    funext i
    rw [RingHom.id_apply, J₂.j_smul, hf', hf', J₁.j_smul, map_smul]
  · intro x
    apply J₂.j_inj
    funext i
    show J₂.j (f (V₁.φ x)) i = J₂.j (V₂.φ (f x)) i
    rw [hf', c₁.1, c₂.1, hf', F.φ_comm]
  · intro x
    apply J₂.j_inj
    funext i
    show J₂.j (f (V₁.γ x)) i = J₂.j (V₂.γ (f x)) i
    rw [hf', c₁.2, c₂.2, hf', F.γ_comm]
  · intro x hx
    refine (J₂.j_N _).2 fun i => ?_
    show J₂.j (f x) i ∈ W₂.N i
    rw [hf']
    exact F.N_le i _ ((J₁.j_N x).1 hx i)

theorem invariants_short_exact : StatInvSES := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E ρ₀ ρ₁ ρ₂ M₀
    D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ V₀ V₁ V₂ J₀ J₁ J₂ c0 c1 c2 hι hπ hsat
  obtain ⟨Gι, hGι⟩ := inv_hom E.ι J₀ J₁ c0 c1 hι
  obtain ⟨Gπ, hGπ⟩ := inv_hom E.π J₁ J₂ c1 c2 hπ
  refine ⟨{ ι := Gι, π := Gπ, ι_inj := ?_, exact := ?_, sat := ?_ }, hGι, hGπ⟩
  · intro x y hxy
    apply J₀.j_inj
    funext i
    apply E.ι_inj i
    rw [← hGι, ← hGι, hxy]
  · intro x
    constructor
    · intro hx
      have h0 : ∀ i, E.π.f i (J₁.j x i) = 0 := by
        intro i
        rw [← hGπ, hx, map_zero]
        rfl
      choose y hy using fun i => (E.exact i _).1 (h0 i)
      have hxinv : ∀ i d, ρ₁ i d (J₁.j x i) = J₁.j x i := (J₁.j_range _).2 ⟨x, rfl⟩
      have hyinv : ∀ i d, ρ₀ i d (y i) = y i := by
        intro i d
        apply E.ι_inj i
        rw [hι, hy, hxinv]
      obtain ⟨x₀, hx₀⟩ := (J₀.j_range y).1 hyinv
      refine ⟨x₀, J₁.j_inj (funext fun i => ?_)⟩
      rw [hGι, hx₀, hy]
    · rintro ⟨x₀, rfl⟩
      apply J₂.j_inj
      funext i
      rw [hGπ, hGι, map_zero]
      exact (E.exact i _).2 ⟨_, rfl⟩
  · intro x₀ hx₀
    refine (J₀.j_N _).2 fun i => hsat i _ ?_
    rw [← hGι]
    exact (J₁.j_N _).1 hx₀ i

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem gamma_sub_one_invariants_holds : GammaSubOneStatedForm := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ κ _ b hs hP2 hρ hρN hb hγρ hcap x hxN hxinv
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  have hγN : ∀ i, ∀ y ∈ W.N i, W.γ i y ∈ W.N i := by
    intro i y hy
    obtain ⟨y', hy', e⟩ := hP2 i y hy
    have : W.γ i y = y + S.X • y' := by rw [← e]; abel
    rw [this]
    exact (W.N i).add_mem hy ((W.N i).smul_mem _ hy')
  have key : ∀ i, ∃ x' : ↥(W.N i), (∀ d, ρ i d (x' : D) = x') ∧
      W.γ i (x i) - x i = IB.j B.X • (x' : D) := by
    intro i
    let ρN : Δ → ↥(W.N i) →+ ↥(W.N i) := fun d =>
      { toFun := fun y => ⟨ρ i d y, hρN i d y y.2⟩
        map_zero' := Subtype.ext (map_zero (ρ i d))
        map_add' := fun y z => Subtype.ext (map_add (ρ i d) _ _) }
    let γN : ↥(W.N i) →+ ↥(W.N i) :=
      { toFun := fun y => ⟨W.γ i y, hγN i y y.2⟩
        map_zero' := Subtype.ext (map_zero (W.γ i))
        map_add' := fun y z => Subtype.ext (map_add (W.γ i) _ _) }
    obtain ⟨x', hx'inv, hx'⟩ := gamma_sub_one_pi_invariants A Δ ↥(W.N i) κ (b i) ρN γN S.π (IB.j B.X)
      (fun d a y => Subtype.ext (hρ i d a y)) (fun d k => Subtype.ext (hb i d k))
      (fun d y => Subtype.ext (hγρ i d y))
      (fun y => by
        obtain ⟨y', hy', e⟩ := hP2 i y y.2
        exact ⟨⟨y', hy'⟩, Subtype.ext (by rw [← hX]; exact e)⟩)
      hcap ⟨x i, hxN i⟩ (fun d => Subtype.ext (hxinv i d))
    exact ⟨x', fun d => congrArg Subtype.val (hx'inv d), congrArg Subtype.val hx'⟩
  choose x' h1 h2 using key
  exact ⟨fun i => x' i, fun i => (x' i).2, h1, h2⟩

theorem delta_basis_holds : StatDeltaBasis := by
  intro O A _ _ _ S Δ _ _ _ ι pr D _ _ _ _ W ρ hR hu hΔ
  obtain ⟨hρ, -, -, htriv, κ, _, hb⟩ := hΔ
  have hρN : ∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i := by
    intro i d x hx
    obtain ⟨x', hx', e⟩ := htriv i d x hx
    have : ρ i d x = x + S.π • x' := by rw [← e]; abel
    rw [this]
    exact (W.N i).add_mem hx ((W.N i).smul_mem _ hx')
  refine ⟨hρN, κ, inferInstance, ?_⟩
  have key : ∀ i, ∃ b' : Module.Basis κ A ↥(W.N i), ∀ d k, ρ i d (b' k : D) = (b' k : D) := by
    intro i
    let ρN : Δ → ↥(W.N i) →+ ↥(W.N i) := fun d =>
      { toFun := fun y => ⟨ρ i d y, hρN i d y y.2⟩
        map_zero' := Subtype.ext (map_zero (ρ i d))
        map_add' := fun y z => Subtype.ext (map_add (ρ i d) _ _) }
    obtain ⟨b', hb'⟩ := invariant_basis_average A Δ ↥(W.N i) κ (hb i).some ρN S.π
      (fun d d' x => Subtype.ext (by
        show ρ i (d * d') (x : D) = ρ i d (ρ i d' (x : D))
        rw [map_mul]; rfl))
      (fun x => Subtype.ext (by
        show ρ i 1 (x : D) = x
        rw [map_one]; rfl))
      (fun d a y => Subtype.ext (hρ i d a y)) hR hu
      (fun d x => by
        obtain ⟨x', hx', e⟩ := htriv i d x x.2
        exact ⟨⟨x', hx'⟩, Subtype.ext e⟩)
    exact ⟨b', fun d k => congrArg Subtype.val (hb' d k)⟩
  choose b' hb' using key
  exact ⟨b', hb'⟩

theorem invariants_exist_holds : StatInvExists := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ hρ hφ hγ
  let T : Submodule O (ι → D) :=
    { carrier := {x | ∀ i d, ρ i d (x i) = x i}
      add_mem' := by
        intro a b ha hb i d
        rw [Pi.add_apply, map_add, ha, hb]
      zero_mem' := by
        intro i d
        rw [Pi.zero_apply, map_zero]
      smul_mem' := by
        intro c x hx i d
        rw [Pi.smul_apply, map_smul, hx] }
  have hinv : ∀ (a : A₀) (d : Δ), d • IB.j a = IB.j a := fun a => (IB.j_range _).2 ⟨a, rfl⟩
  let sm : A₀ → ↥T → ↥T := fun a x => ⟨fun i => IB.j a • x.1 i, fun i d => by
    show ρ i d (IB.j a • x.1 i) = _
    rw [hρ, hinv, x.2 i d]⟩
  letI : Module A₀ ↥T :=
    { smul := sm
      one_smul := fun x => Subtype.ext (funext fun i => by
        show IB.j 1 • x.1 i = x.1 i
        rw [map_one, one_smul])
      mul_smul := fun a b x => Subtype.ext (funext fun i => by
        show IB.j (a * b) • x.1 i = IB.j a • IB.j b • x.1 i
        rw [map_mul, mul_smul])
      smul_zero := fun a => Subtype.ext (funext fun i => by
        show IB.j a • (0 : D) = 0
        rw [smul_zero])
      smul_add := fun a x y => Subtype.ext (funext fun i => by
        show IB.j a • (x.1 i + y.1 i) = IB.j a • x.1 i + IB.j a • y.1 i
        rw [smul_add])
      add_smul := fun a b x => Subtype.ext (funext fun i => by
        show IB.j (a + b) • x.1 i = IB.j a • x.1 i + IB.j b • x.1 i
        rw [map_add, add_smul])
      zero_smul := fun x => Subtype.ext (funext fun i => by
        show IB.j 0 • x.1 i = 0
        rw [map_zero, zero_smul]) }
  haveI : IsScalarTower O A₀ ↥T := ⟨fun o a x => Subtype.ext (funext fun i => by
    show IB.j (o • a) • x.1 i = o • (IB.j a • x.1 i)
    rw [map_smul, smul_assoc])⟩
  let φ' : ↥T →ₗ[O] ↥T :=
    { toFun := fun x => ⟨fun i => W.φ i (x.1 (pr i)), fun i d => by
        show ρ i d (W.φ i (x.1 (pr i))) = _
        rw [← hφ, x.2]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add (W.φ i) _ _)
      map_smul' := fun c x => Subtype.ext (funext fun i => map_smul (W.φ i) _ _) }
  let γ' : ↥T →ₗ[O] ↥T :=
    { toFun := fun x => ⟨fun i => W.γ i (x.1 i), fun i d => by
        show ρ i d (W.γ i (x.1 i)) = _
        rw [← hγ, x.2]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add (W.γ i) _ _)
      map_smul' := fun c x => Subtype.ext (funext fun i => map_smul (W.γ i) _ _) }
  exact ⟨↥T, inferInstance, inferInstance, inferInstance, inferInstance, T.subtype, φ', γ',
    Subtype.val_injective, fun _ _ _ => rfl,
    fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨x', rfl⟩; exact x'.2⟩,
    fun _ _ => rfl, fun _ _ => rfl, hρ⟩

end Formalism.RepresentationBoundsCohomology.JN
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem card_unit (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (hn : n = ℓ - 1) : IsUnit ((n : ℕ) : ℤ_[ℓ]) := by
  have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  rw [hn, Nat.cast_sub (by omega), Nat.cast_one]
  have h0 : IsUnit (1 - (ℓ : ℤ_[ℓ])) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.prime_p.not_isUnit
  have : (ℓ : ℤ_[ℓ]) - 1 = -(1 - (ℓ : ℤ_[ℓ])) := by ring
  rw [this]
  exact h0.neg

theorem card_unit' (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (n : ℕ)
    (hn : n = ℓ - 1) : IsUnit ((n : ℕ) : A) := by
  have := (card_unit ℓ n hn).map (algebraMap ℤ_[ℓ] A)
  rwa [map_natCast] at this

theorem extension_nonlinear_holds : StatExtNL := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D _ _ _ _ W ρ M₀ D' _ _ _ _ V J Hh _ _ cl Hf M h H hs hR
    hD hP2 hP5 hL hM hH hcard hΔ hGQ hcap hJ hE κ hκ
  obtain ⟨Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, e, p2p, p2t, p5p, p5t, lp, lt, p6,
    dp, dt, hι, hπ, he, hφe, hγe, hρe, hdict⟩ := hE κ hκ
  obtain ⟨np, κp, _, bp, hbp⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr Dp Wp ρp hR (card_unit' ℓ A _ hcard) dp
  obtain ⟨nt, κt, _, bt, hbt⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr Dt Wt ρt hR (card_unit' ℓ A _ hcard) dt
  obtain ⟨sp, fp, gp, -, -⟩ := dp
  obtain ⟨st, ft, gt, -, -⟩ := dt
  obtain ⟨Dp', k1, k2, k3, k4, jp, φp, γp, x1, x2, x3, x4, x5, x6⟩ :=
    invariants_exist_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp sp fp gp
  obtain ⟨Dt', m1, m2, m3, m4, jt, φt, γt, y1, y2, y3, y4, y5, y6⟩ :=
    invariants_exist_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt st ft gt
  have g9p := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp κp bp hs p2p sp np hbp gp hcap
  have g9t := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt κt bt hs p2t st nt hbt gt hcap
  obtain ⟨Vp, Jp, ep, epφ, epγ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dp Wp ρp M h M₀ Dp' jp φp γp hs
    hΔ hGQ p5p hM x1 x2 x3 x4 x5 x6 g9p
  obtain ⟨Vt, Jt, et, etφ, etγ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr Dt Wt ρt M h M₀ Dt' jt φt γt hs
    hΔ hGQ p5t hM y1 y2 y3 y4 y5 y6 g9t
  obtain ⟨-, -, -, hsat, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D Dp Dt W Wp Wt E M h M₀ H H hR hD hP2 p2p p2t hP5
    p5p p5t hL lp lt p6 hM (fun i => by have := hH i; omega) hH
  have cp : Jp.Compat := ⟨by rw [ep, epφ]; exact x4, by rw [ep, epγ]; exact x5⟩
  have ct : Jt.Compat := ⟨by rw [et, etφ]; exact y4, by rw [et, etγ]; exact y5⟩
  obtain ⟨Sq, hSι, hSπ⟩ := invariants_short_exact ℤ_[ℓ] A A₀ S B Δ IB ι pr D Dp Dt W Wp Wt E ρ ρp ρt M₀ D' Dp' Dt'
    V Vp Vt J Jp Jt hJ cp ct hι hπ hsat
  obtain ⟨e', he'⟩ := (Jt.j_range e).1 hρe
  refine ⟨{ Dp := Dp', Dt := Dt', Wp := Vp, Wt := Vt, S := Sq, e := e', e_mem := ?_, φe := ?_,
            γe := ?_ }, Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, Jp, Jt, p2p, p2t, p5p,
    p5t, lp, lt, p6, cp, ct, ⟨np, hπ, st⟩, hSπ, ?_⟩
  · exact (Jt.j_N e').2 fun i => by rw [he']; exact he i
  · exact Jt.j_inj (funext fun i => by rw [ct.1, he', hφe])
  · exact Jt.j_inj (funext fun i => by rw [ct.2, he', hγe])
  · intro c x p h1 h2 h3
    refine hdict c (Jp.j x) p ((Jp.j_range _).2 ⟨x, rfl⟩) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · have h1' : Sq.π.f x = c • e' := h1
      rw [← hSπ, h1', map_smul, he']
      rfl
    · have h2' : Sq.ι.f (p : D' × D').1 = Vp.φ x - x := h2
      rw [← hSι, h2', map_sub, Pi.sub_apply, cp.1]
    · have h3' : Sq.ι.f (p : D' × D').2 = Vp.γ x - x := h3
      rw [← hSι, h3', map_sub, Pi.sub_apply, cp.2]

theorem lift_case_a_odd_prime : LiftCaseAOddPrime := by
  intro ℓ _ hℓ2 A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ j₀ j₁ j₂ φ₀ γ₀ φ₁ γ₁ φ₂ γ₂ u jumps hℓ hs hc hu hR hD
    a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac i0 i1 i2 d0 d1 d2
    hι hπ hnt
  have hGQ := gamma_quotient_case_a ℤ_[ℓ] A₀ B hQL hdiv hjac
  obtain ⟨n0, κ0, _, β0, hβ0⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₀ W₀ ρ₀ hR (card_unit' ℓ A _ hcard) d0
  obtain ⟨n1, κ1, _, β1, hβ1⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₁ W₁ ρ₁ hR (card_unit' ℓ A _ hcard) d1
  obtain ⟨n2, κ2, _, β2, hβ2⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₂ W₂ ρ₂ hR (card_unit' ℓ A _ hcard) d2
  obtain ⟨s0, -, q0, -, -⟩ := d0
  obtain ⟨s1, -, q1, -, -⟩ := d1
  obtain ⟨s2, -, q2, -, -⟩ := d2
  have g0 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ κ0 β0 hs a0 s0 n0 hβ0 q0 hcap
  have g1 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ κ1 β1 hs a1 s1 n1 hβ1 q1 hcap
  have g2 := gamma_sub_one_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ κ2 β2 hs a2 s2 n2 hβ2 q2 hcap
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := i0
  obtain ⟨y1, y2, y3, y4, y5, y6⟩ := i1
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := i2
  obtain ⟨V₀, J₀, e0, e0φ, e0γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ M h M₀ D₀' j₀ φ₀ γ₀ hs
    hΔ hGQ b0 hM x1 x2 x3 x4 x5 x6 g0
  obtain ⟨V₁, J₁, e1, e1φ, e1γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ M h M₀ D₁' j₁ φ₁ γ₁ hs
    hΔ hGQ b1 hM y1 y2 y3 y4 y5 y6 g1
  obtain ⟨V₂, J₂, e2, e2φ, e2γ⟩ := wach_invariants_holds ℤ_[ℓ] A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ M h M₀ D₂' j₂ φ₂ γ₂ hs
    hΔ hGQ b2 hM z1 z2 z3 z4 z5 z6 g2
  obtain ⟨-, -, -, hsat, -⟩ := wach_top_statement ℤ_[ℓ] A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H H hR hD a0 a1 a2 b0 b1
    b2 c0 c1 c2 hP6 hM (fun i => by have := hH i; omega) hH
  have k0 : J₀.Compat := ⟨by rw [e0, e0φ]; exact x4, by rw [e0, e0γ]; exact x5⟩
  have k1 : J₁.Compat := ⟨by rw [e1, e1φ]; exact y4, by rw [e1, e1γ]; exact y5⟩
  have k2 : J₂.Compat := ⟨by rw [e2, e2φ]; exact z4, by rw [e2, e2γ]; exact z5⟩
  obtain ⟨Sq, hSι, hSπ⟩ := invariants_short_exact ℤ_[ℓ] A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E ρ₀ ρ₁ ρ₂ M₀ D₀' D₁'
    D₂' V₀ V₁ V₂ J₀ J₁ J₂ k0 k1 k2 hι hπ hsat
  refine ⟨V₀, V₁, V₂, Sq, J₀, J₁, J₂, ⟨e0, e0φ, e0γ⟩, ⟨e1, e1φ, e1γ⟩, ⟨e2, e2φ, e2γ⟩, hSι, hSπ, ?_⟩
  intro δ R P ρ κ _ _ _ _ _ _ _ L H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g _ hδ hP4 hj hnat hc1 hc2 hinj he1 he2
    hrat
  exact composition_case_a ℓ hℓ2 A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' V₀ V₁ V₂
    Sq J₀ J₁ J₂ u jumps δ R P ρ κ L H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g hℓ hs hc hu hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2
    hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac k0 k1 k2 ⟨n1, hπ, s2⟩ hSπ hδ hnt hP4 hj hnat hc1
    hc2 hinj
    (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ M₀ D₁' V₁ J₁ H₁ cl₁ Hf₁ M h H hs hR hD a1 b1 c1 hM hH
      hcard hΔ hGQ hcap k1 he1)
    (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ M₀ D₂' V₂ J₂ H₂ cl₂ Hf₂ M h H hs hR hD a2 b2 c2 hM hH
      hcard hΔ hGQ hcap k2 he2) hrat

end Formalism.RepresentationBoundsCohomology.JN
end
end
