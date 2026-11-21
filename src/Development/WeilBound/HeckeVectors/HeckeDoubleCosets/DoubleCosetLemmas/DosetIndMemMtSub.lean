import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GaussBinomialTwistedSumIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosetsStatement

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem absV_mul (x y : Cv v) : absV v (x * y) = absV v x * absV v y := by simp [absV]

theorem absV_nonneg (x : Cv v) : 0 ≤ absV v x := NNReal.coe_nonneg _

theorem absV_one : absV v (1 : Cv v) = 1 := by simp [absV]

theorem absV_pow (x : Cv v) (j : ℕ) : absV v (x ^ j) = absV v x ^ j := by simp [absV]

theorem absV_inv (x : Cv v) : absV v x⁻¹ = (absV v x)⁻¹ := by simp [absV]

theorem absV_unif {ϖ : Cv v} (h : IsUnifV K v ϖ) : absV v ϖ = ((qV K v : ℝ))⁻¹ := by
  unfold absV
  rw [h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe,
    toAdd_ofAdd, _root_.zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]
  rfl

theorem absV_unit (u : (𝒪)ˣ) : absV v (algebraMap 𝒪 (Cv v) u) = 1 := by
  have h : Valued.v (algebraMap 𝒪 (Cv v) u) = 1 :=
    (Valuation.Integers.one_of_isUnit (Valuation.valuationSubring.integers _) u.isUnit)
  rw [absV, h, map_one, NNReal.coe_one]

def wt (s : ℝ) {m : ℕ} (g : GL (Fin m) (Cv v)) : ℂ := ((absV v g.1.det ^ s : ℝ) : ℂ)

theorem wt_one (s : ℝ) {m : ℕ} : wt s (1 : GL (Fin m) (Cv v)) = 1 := by simp [wt, absV_one]

theorem wt_mul (s : ℝ) {m : ℕ} (g h : GL (Fin m) (Cv v)) : wt s (g * h) = wt s g * wt s h := by
  simp only [wt, Units.val_mul, det_mul, absV_mul, Real.mul_rpow (absV_nonneg _) (absV_nonneg _),
    Complex.ofReal_mul]

def rep {X : Type} {m : ℕ} (s : ℝ) (a : X → GL (Fin m) (Cv v) → X) (a1 : ∀ y, a y 1 = y)
    (am : ∀ y g h, a y (g * h) = a (a y g) h) : Representation ℂ (GL (Fin m) (Cv v)) (X → ℂ) where
  toFun g :=
    { toFun := fun Φ y => wt s g * Φ (a y g)
      map_add' := fun Φ Ψ => funext fun y => by simp [mul_add]
      map_smul' := fun c Φ => funext fun y => by simp [mul_left_comm] }
  map_one' := by ext Φ y; simp [wt_one, a1]
  map_mul' g h := by ext Φ y; simp [wt_mul, am, mul_assoc]

variable (v) in

def rS (n c : ℕ) : Representation ℂ (GL (Fin c) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((n : ℝ) / 2) (fun y g => y * g.1) (by simp) (by simp [Matrix.mul_assoc])

variable (v) in

def rT (n c : ℕ) : Representation ℂ (GL (Fin n) (Cv v)) (Matrix (Fin n) (Fin c) (Cv v) → ℂ) :=
  rep ((c : ℝ) / 2) (fun y z => z.1ᵀ * y) (by simp)
    (by simp [Matrix.mul_assoc, Matrix.transpose_mul])

theorem rS_apply {n c : ℕ} (g : GL (Fin c) (Cv v)) (Φ) (y) :
    rS v n c g Φ y = wt ((n : ℝ) / 2) g * Φ (y * g.1) := rfl

theorem rT_apply {n c : ℕ} (z : GL (Fin n) (Cv v)) (Φ) (y) :
    rT v n c z Φ y = wt ((c : ℝ) / 2) z * Φ (z.1ᵀ * y) := rfl


variable (v) in

def phi0 (n c : ℕ) : Matrix (Fin n) (Fin c) (Cv v) → ℂ :=
  Set.indicator {x | ∀ i j, Valued.v (x i j) ≤ 1} 1

theorem intM_iff' {n c : ℕ} {y : Matrix (Fin n) (Fin c) (Cv v)} :
    IntM 𝒪 y ↔ ∀ i j, Valued.v (y i j) ≤ 1 :=
  forall₂_congr fun _ _ => ⟨fun ⟨o, h⟩ => h ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

open Classical in
theorem characteristic_function_integral_apply {n c : ℕ} (y : Matrix (Fin n) (Fin c) (Cv v)) :
    phi0 v n c y = if IntM 𝒪 y then 1 else 0 := by
  unfold phi0
  by_cases h : IntM 𝒪 y
  · rw [if_pos h, Set.indicator_of_mem (show y ∈ {x | ∀ i j, Valued.v (x i j) ≤ 1} from intM_iff'.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem
      (show y ∉ {x | ∀ i j, Valued.v (x i j) ≤ 1} from fun h' => h (intM_iff'.2 h'))]

theorem mem_KGL {m : ℕ} {g : GL (Fin m) (Cv v)} : g ∈ KGL v m ↔ GInt 𝒪 g :=
  ⟨fun h => ⟨intM_iff'.2 fun i j => P.cartan_entries_of_mem _ _ h i j,
    intM_iff'.2 fun i j => P.cartan_entries_of_mem _ _ (inv_mem h) i j⟩,
    fun h => P.cartan_mem_of_entries _ _ (intM_iff'.1 h.1) (intM_iff'.1 h.2)⟩

theorem wt_of_mem (s : ℝ) {m : ℕ} {g : GL (Fin m) (Cv v)} (h : g ∈ KGL v m) : wt s g = 1 := by
  obtain ⟨u, hu⟩ := (mem_KGL.1 h).det
  rw [wt, hu, absV_unit, Real.one_rpow, Complex.ofReal_one]


theorem intM_tr_iff {n c : ℕ} (z : Matrix (Fin n) (Fin n) (Cv v))
    (y : Matrix (Fin n) (Fin c) (Cv v)) : IntM 𝒪 (zᵀ * y) ↔ IntM 𝒪 (yᵀ * z) :=
  ⟨fun h => by simpa [Matrix.transpose_mul] using h.transpose,
    fun h => by simpa [Matrix.transpose_mul] using h.transpose⟩



theorem heckeVec_apply {G X : Type} [Group G] {J : Subgroup G} (hJ : IsCommensurated J)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ J) (ρ : Representation ℂ G (X → ℂ)) (Φ : X → ℂ) (y : X) :
    heckeVec ρ J h Φ y = ∑ᶠ c : G ⧸ J, h c.out * ρ c.out Φ y :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) y).toAddMonoidHom.map_finsum
    (finite_heckeVec hJ hh ρ Φ)

theorem hk_tor {p : 𝒪} (h0 : (p : Cv v) ≠ 0) {m j : ℕ} (hj : j ≤ m) :
    Hk 𝒪 p j (tor h0 fun i : Fin m => if (i : ℕ) < j then 1 else 0) := by
  refine ⟨intM_iff'.2 fun a b => ?_, intM_iff'.2 fun a b => ?_, 1, ?_⟩
  · rw [tor_val, diagonal_apply]
    split_ifs
    · rw [zpow_one]; exact p.2
    · simp
    · simp
  · change Valued.v ((p : Cv v) * diagonal (fun i : Fin m =>
      (p : Cv v) ^ (-(if (i : ℕ) < j then 1 else 0 : ℤ))) a b) ≤ 1
    rw [diagonal_apply]
    split_ifs
    · simp [h0]
    · rw [neg_zero, zpow_zero, mul_one]; exact p.2
    · simp
  · rw [tor_val, det_diagonal]
    simp only [apply_ite (fun e : ℤ => (p : Cv v) ^ e), zpow_one, zpow_zero]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt,
      min_eq_right hj]
    simp

open Classical in

theorem Tj_count {X : Type} {m j : ℕ} (hj : j ≤ m) {p : 𝒪} (hp : IsUnifV K v (p : Cv v))
    (h0 : (p : Cv v) ≠ 0) : ∃ R : Finset (GL (Fin m) (Cv v) ⧸ KGL v m),
      Reps 𝒪 (tor h0 fun i : Fin m => if (i : ℕ) < j then 1 else 0) R Quotient.out ∧
      ∀ (s : ℝ) (ρ : Representation ℂ (GL (Fin m) (Cv v)) (X → ℂ)) (Φ : X → ℂ) (y : X)
        (Q : GL (Fin m) (Cv v) → Prop), (∀ g, ρ g Φ y = wt s g * if Q g then 1 else 0) →
        heckeVec ρ (KGL v m) (Tj ℂ m (Ov K v) p j) Φ y =
          ((((qV K v : ℝ)⁻¹ ^ j) ^ s : ℝ) : ℂ) * Nat.card {γ // γ ∈ R ∧ Q γ.out} := by
  have hK : IsCommensurated (KGL v m) := Final.GLintComm K v m
  set α := tor h0 fun i : Fin m => if (i : ℕ) < j then (1 : ℤ) else 0
  have hf := P.finite_support_cosets hK (Final.DosetIndMem _ (KGL v m) ℂ α).2
  have hR : ∀ γ, γ ∈ hf.toFinset ↔ ∃ a ∈ KGL v m, ∃ b ∈ KGL v m, γ.out = a * α * b := fun γ => by
    rw [Set.Finite.mem_toFinset]
    refine ⟨fun h => by_contra fun h' => h (dosetInd_of_not h'), fun h => ?_⟩
    change dosetInd ℂ _ α γ.out ≠ 0
    rw [dosetInd_of_mem h]; exact one_ne_zero
  refine ⟨hf.toFinset, ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩, fun s ρ Φ y Q hQ => ?_⟩
  · obtain ⟨a, ha, b, hb, e⟩ := (hR γ).1 hγ
    exact ⟨a, b, mem_KGL.1 ha, mem_KGL.1 hb, e⟩
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL v m) (k₁ * α * k₂)
    refine ⟨(k₁ * α * k₂ : GL (Fin m) (Cv v)), ⟨(hR _).2 ⟨k₁, mem_KGL.2 h₁, k₂ * k,
      mul_mem (mem_KGL.2 h₂) k.2, by rw [hk]; group⟩, mem_KGL.1 ?_⟩, fun γ hγ => ?_⟩
    · rw [hk]
      rw [show (k₁ * α * k₂ * k)⁻¹ * (k₁ * α * k₂) = (k : GL (Fin m) (Cv v))⁻¹ by group]
      exact inv_mem k.2
    · rw [← γ.out_eq']
      exact QuotientGroup.eq.2 (mem_KGL.2 hγ.2)
  · rw [heckeVec_apply hK (Tj_mem_hecke hp j), Tj_eq h0,
      finsum_eq_sum_of_support_subset (s := hf.toFinset) _ fun γ hγ => by
        rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hγ]
    have e : ∀ γ ∈ hf.toFinset, dosetInd ℂ (KGL v m) α γ.out * ρ γ.out Φ y =
        ((((qV K v : ℝ)⁻¹ ^ j) ^ s : ℝ) : ℂ) * if Q γ.out then 1 else 0 := fun γ hγ => by
      obtain ⟨a, ha, b, hb, e⟩ := (hR γ).1 hγ
      obtain ⟨u, hu⟩ := (hk_tor h0 hj).2.2
      rw [dosetInd_of_mem ⟨a, ha, b, hb, e⟩, one_mul, hQ]
      congr 1
      rw [e, wt_mul, wt_mul, wt_of_mem _ ha, wt_of_mem _ hb, one_mul, mul_one, wt, hu, map_mul,
        absV_mul, absV_unit, mul_one, map_pow, absV_pow]
      exact congrArg (fun t : ℝ => (((t ^ j) ^ s : ℝ) : ℂ)) (absV_unif hp)
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_boole,
      Nat.subtype_card (hf.toFinset.filter fun γ => Q γ.out) (by simp)]

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem card_res : Nat.card (IsLocalRing.ResidueField 𝒪) = qV K v :=
  GlobalTheory.SplitUnif.card_residueField v (algebraMap K (Cv v)) v (fun _ => rfl) fun x => by
    rw [← v.valuation_lt_one_iff_mem (K := K)]
    exact (congrArg (· < 1) (v.valuedAdicCompletion_eq_valuation' (x : K))).to_iff.symm

theorem cst (q j m : ℕ) : (((((q : ℝ)⁻¹ ^ j) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) =
    ((Real.sqrt q : ℂ) ^ m)⁻¹ ^ j := by
  have h : (((q : ℝ)⁻¹ ^ j) ^ ((m : ℝ) / 2) : ℝ) = (Real.sqrt q ^ m)⁻¹ ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity),
      Real.rpow_natCast, Real.inv_rpow (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast ((q : ℝ) ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul (by positivity)]
    congr 3
    ring
  rw [h]; push_cast; rfl

section Count

variable {l m j : ℕ} {α : GL (Fin m) (Cv v)} {ι : Type} {R : Finset ι}
  {ρ : ι → GL (Fin m) (Cv v)}

theorem cnt_zero {p : 𝒪} (hα : Hk 𝒪 p j α) (hR : Reps 𝒪 α R ρ) {y : Matrix (Fin l) (Fin m) (Cv v)}
    (hy : ¬ IntM 𝒪 (algebraMap 𝒪 (Cv v) p • y)) :
    Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * (ρ γ).1)} = 0 := by
  refine Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨γ, hγ, h⟩ => hy ?_⟩)
  obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 γ hγ
  have hk : Hk 𝒪 p j (ρ γ) := h4 ▸ hα.mul g₁ g₂
  have := h.mul hk.2.1
  rwa [Matrix.mul_smul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at this

theorem cnt_eq {p : 𝒪} (hp : Irreducible p) (hj : j ≤ m) (hα : Hk 𝒪 p j α) (hR : Reps 𝒪 α R ρ)
    {y : Matrix (Fin l) (Fin m) (Cv v)} {w : Matrix (Fin l) (Fin m) (IsLocalRing.ResidueField 𝒪)}
    (hy : IntM 𝒪 (y - yw (Cv v) p w)) :
    Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * (ρ γ).1)} = nKer j w := by
  rw [← GlobalTheory.SplitHecke.card_heckeCosetReps_integral_right_inversePrime hp hj hα hR w]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun hγ => ?_)
  obtain ⟨k₁, k₂, g₁, g₂, h4⟩ := hR.1 γ hγ
  have hk : Hk 𝒪 p j (ρ γ) := h4 ▸ hα.mul g₁ g₂
  have h1 := hy.mul hk.1
  rw [Matrix.sub_mul] at h1
  exact ⟨fun h => by simpa using h.sub h1, fun h => by simpa using h1.add h⟩

end Count

theorem heckeVec_sum_left {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    (hJ : IsCommensurated J) (ρ : Representation ℂ G V) (s : Finset ι) (a : ι → ℂ)
    (f : ι → G → ℂ) (hf : ∀ i, f i ∈ Hecke ℂ J) (x : V) :
    heckeVec ρ J (∑ i ∈ s, a i • f i) x = ∑ i ∈ s, a i • heckeVec ρ J (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [heckeVec]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, heckeVec_add_left hJ
      (Submodule.smul_mem _ _ (hf i))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)), heckeVec_smul_left hJ (hf i), ih]

def Acts {m : ℕ} (f : GL (Fin m) (Cv v) → ℂ) (B : Multiset ℂˣ) (lam : ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V),
    IsSatVecGL v ρ x B → heckeVec ρ (KGL v m) f x = lam • x

def Mt (c t : ℕ) (f' : GL (Fin (c + t)) (Cv v) → ℂ) (f : GL (Fin c) (Cv v) → ℂ) : Prop :=
  f' ∈ Hecke ℂ (KGL v (c + t)) ∧ f ∈ Hecke ℂ (KGL v c) ∧
    heckeVec (rT v (c + t) c) (KGL v (c + t)) f' (phi0 v (c + t) c) =
      heckeVec (rS v (c + t) c) (KGL v c) f (phi0 v (c + t) c) ∧
    ∀ B : Multiset ℂˣ, B.card = c → ∃ lam, Acts f B lam ∧ Acts f' (B + seg v 1 t) lam

variable (v) in

def mtSub (c t : ℕ) : Submodule ℂ (GL (Fin (c + t)) (Cv v) → ℂ) where
  carrier := {f' | ∃ f, Mt c t f' f}
  zero_mem' := ⟨0, zero_mem _, zero_mem _, by simp [heckeVec], fun B _ =>
    ⟨0, fun V _ _ ρ x _ => by simp [heckeVec], fun V _ _ ρ x _ => by simp [heckeVec]⟩⟩
  add_mem' := by
    rintro f' g' ⟨f, a1, a2, a3, a4⟩ ⟨g, b1, b2, b3, b4⟩
    have hK := Final.GLintComm K v c
    have hK' := Final.GLintComm K v (c + t)
    refine ⟨f + g, add_mem a1 b1, add_mem a2 b2, by
      rw [heckeVec_add_left hK' a1 b1, heckeVec_add_left hK a2 b2, a3, b3], fun B hB => ?_⟩
    obtain ⟨l, l1, l2⟩ := a4 B hB
    obtain ⟨l', m1, m2⟩ := b4 B hB
    exact ⟨l + l', fun V _ _ ρ x hx => by
      rw [heckeVec_add_left hK a2 b2, l1 V ρ x hx, m1 V ρ x hx, add_smul], fun V _ _ ρ x hx => by
      rw [heckeVec_add_left hK' a1 b1, l2 V ρ x hx, m2 V ρ x hx, add_smul]⟩
  smul_mem' := by
    rintro z f' ⟨f, a1, a2, a3, a4⟩
    have hK := Final.GLintComm K v c
    have hK' := Final.GLintComm K v (c + t)
    refine ⟨z • f, Submodule.smul_mem _ z a1, Submodule.smul_mem _ z a2, by
      rw [heckeVec_smul_left hK' a1, heckeVec_smul_left hK a2, a3], fun B hB => ?_⟩
    obtain ⟨l, l1, l2⟩ := a4 B hB
    exact ⟨z * l, fun V _ _ ρ x hx => by rw [heckeVec_smul_left hK a2, l1 V ρ x hx, mul_smul],
      fun V _ _ ρ x hx => by rw [heckeVec_smul_left hK' a1, l2 V ρ x hx, mul_smul]⟩


set_option maxHeartbeats 1000000 in
theorem Tj_mem_mtSub {c t : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (d : ℕ) (hd : d ≤ c + t) :
    Tj ℂ (c + t) (Ov K v) ϖ d ∈ mtSub v c t := by
  classical
  have hK : IsCommensurated (KGL v c) := Final.GLintComm K v c
  obtain ⟨p, rfl⟩ : ∃ p : 𝒪, (p : Cv v) = ϖ := ⟨⟨ϖ, mem_Ov_of_isUnifV hu⟩, rfl⟩
  have h0 := ne_zero_of_isUnifV hu
  have hp : Irreducible p := GlobalTheory.SplitUnif.irreducible_of_valued v p hu
  set q := qV K v with hq
  let a : ℕ → ℂ := fun j => (q : ℂ) ^ ((c - j) * (d - j)) * (Formalism.L2.Col.gaussBin q t (d - j) : ℂ) *
    ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d * ((Real.sqrt q : ℂ) ^ (c + t)) ^ j
  have hjc : ∀ j ∈ Finset.range (min d c + 1), j ≤ c := fun j hj => by
    have := Finset.mem_range.1 hj; omega
  refine ⟨∑ j ∈ Finset.range (min d c + 1), a j • Tj ℂ c (Ov K v) p j, Tj_mem_hecke hu d,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Tj_mem_hecke hu j), ?_,
    fun B hB => ⟨satEig q (c + t) (B + seg v 1 t) d, fun V _ _ ρ x hx => ?_,
      fun V _ _ ρ x hx => hx.2.2.2 _ hu d hd⟩⟩
  · rw [heckeVec_sum_left hK _ _ _ _ (Tj_mem_hecke hu)]
    funext y
    obtain ⟨RT, hRT, eT⟩ := Tj_count (X := Matrix (Fin (c + t)) (Fin c) (Cv v)) hd hu h0
    rw [eT _ _ _ y (fun z => IntM 𝒪 (yᵀ * z.1)) (fun z => by
      rw [rT_apply, characteristic_function_integral_apply, intM_tr_iff]), cst, Finset.sum_apply]
    have eS : ∀ j ∈ Finset.range (min d c + 1), ∀ N : ℕ,
        (∀ R : Finset (GL (Fin c) (Cv v) ⧸ KGL v c),
          Reps 𝒪 (tor h0 fun i : Fin c => if (i : ℕ) < j then 1 else 0) R Quotient.out →
          Nat.card {γ // γ ∈ R ∧ IntM 𝒪 (y * γ.out.1)} = N) →
        (a j • heckeVec (rS v (c + t) c) (KGL v c) (Tj ℂ c (Ov K v) p j) (phi0 v (c + t) c)) y =
          ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d *
            ((q ^ ((c - j) * (d - j)) * Formalism.L2.Col.gaussBin q t (d - j) * N : ℕ) : ℂ) := by
      intro j hj N hN
      obtain ⟨R, hR, e⟩ := Tj_count (X := Matrix (Fin (c + t)) (Fin c) (Cv v)) (hjc j hj) hu h0
      have hs : ((Real.sqrt q : ℂ) ^ (c + t)) ≠ 0 := pow_ne_zero _ (by
        have : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (qV_ne_zero v)
        exact_mod_cast (Real.sqrt_pos.2 this).ne')
      rw [Pi.smul_apply, e _ _ _ y (fun g => IntM 𝒪 (y * g.1)) (fun g => by
        rw [rS_apply, characteristic_function_integral_apply]), cst, hN R hR, smul_eq_mul]
      rw [← hq]
      simp only [a]
      generalize (Real.sqrt q : ℂ) ^ (c + t) = u at hs ⊢
      generalize ((Real.sqrt q : ℂ) ^ c)⁻¹ ^ d = u'
      push_cast
      rw [inv_pow]
      field_simp
    by_cases hy : IntM 𝒪 (algebraMap 𝒪 (Cv v) p • y)
    · obtain ⟨w, hw, -⟩ := GlobalTheory.SplitHecke.existsUnique_yw hp hy
      haveI : Finite (IsLocalRing.ResidueField 𝒪) :=
        Nat.finite_of_card_ne_zero (card_res (v := v) ▸ qV_ne_zero v)
      rw [cnt_eq hp hd (hk_tor h0 hd) hRT (y := yᵀ) (w := wᵀ) hw.transpose,
        Finset.sum_congr rfl fun j hj => eS j hj (nKer j w) fun R hR =>
          cnt_eq hp (hjc j hj) (hk_tor h0 (hjc j hj)) hR hw,
        ← Finset.mul_sum, GlobalTheory.SplitHecke.nKer_eq_sum (t := t) rfl, card_res, Nat.cast_sum]
      rfl
    · rw [cnt_zero (hk_tor h0 hd) hRT (y := yᵀ) fun h => hy h.transpose,
        Finset.sum_congr rfl fun j hj => eS j hj 0 fun R hR =>
          cnt_zero (hk_tor h0 (hjc j hj)) hR hy]
      simp
  · have e := GlobalTheory.T.gaussBinomial_twisted_sum_identity v c t d B 1 1 hB hd
    simp only [Units.val_one, one_mul, inv_one, mul_one, Multiset.map_id'] at e
    rw [heckeVec_sum_left hK _ _ _ _ (Tj_mem_hecke hu),
      Finset.sum_congr rfl fun j hj => by rw [hx.2.2.2 _ hu j (hjc j hj), smul_smul],
      ← Finset.sum_smul]
    exact congrArg (· • x) e

end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
end

section
noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.WeylGL
open GlobalTheory.LFun.SatCompare GlobalTheory.CompanionTheory.Ipf.Val
open GlobalTheory.SplitHecke (IntM GInt Hk Reps tr yw nKer)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers K v

theorem heckeVec_central {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {J : Subgroup G}
    {ρ : Representation ℂ G V} {x : V} (hx : x ∈ fixed ρ J) {z : G} (hz : ∀ g, z * g = g * z) :
    heckeVec ρ J (dosetInd ℂ J z) x = ρ z x := by
  rw [heckeVec_dosetInd hx (R := {z}) (by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩) (by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hz a, show z⁻¹ * (z * a * b) = a * b by group]
    exact mul_mem ha hb), Finset.sum_singleton]












def theta (m : ℕ) : GL (Fin m) (Cv v) ≃* GL (Fin m) (Cv v) where
  toFun g := tr g⁻¹
  invFun g := tr g⁻¹
  left_inv _ := Units.ext rfl
  right_inv _ := Units.ext rfl
  map_mul' g h := by rw [_root_.mul_inv_rev, GlobalTheory.SplitHecke.tr_mul]

theorem theta_theta {m : ℕ} (g : GL (Fin m) (Cv v)) : theta m (theta m g) = g := Units.ext rfl

theorem theta_mem {m : ℕ} (g : GL (Fin m) (Cv v)) : g ∈ KGL v m ↔ theta m g ∈ KGL v m := by
  rw [mem_KGL, mem_KGL]
  exact (GlobalTheory.SplitHecke.gInt_tr.trans GlobalTheory.SplitHecke.gInt_inv).symm

theorem theta_tor {m : ℕ} {ϖ : Cv v} (h0 : ϖ ≠ 0) (a : Fin m → ℤ) :
    theta m (tor h0 a) = (tor h0 a)⁻¹ := Units.ext (diagonal_transpose _)





theorem exists_sat (m : ℕ) (B : Multiset ℂˣ) (hB : B.card = m) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ (GL (Fin m) (Cv v)) V) (x : V), IsSatVecGL v ρ x B := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = m := hB
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨x, hx⟩ := (hasSatGL_psFunGL (w := v) α).exists_vec
  exact ⟨_, _, _, _, x, hx⟩

theorem hecke_eq_sum {m : ℕ} {ϖ : Cv v} (hu : IsUnifV K v ϖ) (h0 : ϖ ≠ 0)
    {f : GL (Fin m) (Cv v) → ℂ} (hf : f ∈ Hecke ℂ (KGL v m)) :
    ∃ (I : Finset (Fin m → ℤ)) (a : (Fin m → ℤ) → ℂ),
      f = ∑ e ∈ I, a e • dosetInd ℂ (KGL v m) (tor h0 e) := by
  have : f ∈ Submodule.span ℂ (Set.range fun e : Fin m → ℤ => dosetInd ℂ (KGL v m) (tor h0 e)) :=
    mem_of_supp _ hf fun g _ => by
      obtain ⟨a, -, hg⟩ := cartan h0 hu g
      rw [dosetInd_congr hg]
      exact Submodule.subset_span ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨a.support, a, ha.symm⟩




end CompanionTheory.D.Upq.DoubleCosetLemmas.Mch

end
end
