import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogCombinationFiniteLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleValueExpansionEqLogDerivSmul

section
section
open GlobalTheory.K5

namespace GlobalTheory.CuspCup

theorem cup_identity {R : Type*} [CommRing R]
    (N P A B A' B' i m ag bg bh bgh qg qh qgh zg zh zgh x gx gy ghy e₁ e₂ tb tq tz : R)
    (h₁ : P * ag - A * qg - B * zg - (gx - x) = N * e₁)
    (h₂ : P * bh - A' * qh - B' * zh - (ghy - gy) = N * e₂)
    (hb : bgh = bg + bh - N * tb) (hq : qgh = qg + qh - N * tq) (hz : zgh = zg + zh - N * tz)
    (hi : 2 * i = 1 + N * m) :
    (P * ag) * (P * bh) + (A * B' - B * A') * (zg * qh) -
      ((gx * (P * bh) - (A * qh + B * zh) * ghy - i * (A * A') * qh ^ 2 - A * B' * (qh * zh)
          - i * (B * B') * zh ^ 2)
        - (x * (P * bgh) - (A * qgh + B * zgh) * ghy - i * (A * A') * qgh ^ 2
          - A * B' * (qgh * zgh) - i * (B * B') * zgh ^ 2)
        + (x * (P * bg) - (A * qg + B * zg) * gy - i * (A * A') * qg ^ 2 - A * B' * (qg * zg)
          - i * (B * B') * zg ^ 2)) =
    N * (e₁ * (P * bh) + (A * qg + B * zg) * e₂ - P * x * tb + (A * tq + B * tz) * ghy
      - m * (A * A') * (qg * qh) - m * (B * B') * (zg * zh)
      + i * (A * A') * (2 * tq * (qg + qh) - N * tq ^ 2)
      + A * B' * (tq * (zg + zh) + tz * (qg + qh) - N * (tq * tz))
      + i * (B * B') * (2 * tz * (zg + zh) - N * tz ^ 2)) := by
  subst hb hq hz
  linear_combination (P * bh) * h₁ + (A * qg + B * zg) * h₂
    - (A * A' * (qg * qh) + B * B' * (zg * zh)) * hi

theorem exists_val_add {R : Type*} [CommRing R] (p n : ℕ) (hp : p ≠ 0) (u v : ZMod (p ^ n)) :
    ∃ t : ℕ, (((u + v).val : ℕ) : R) = (u.val : R) + (v.val : R) - (p : R) ^ n * (t : R) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp⟩
  refine ⟨(u.val + v.val) / p ^ n, ?_⟩
  have h := Nat.mod_add_div (u.val + v.val) (p ^ n)
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → R) h
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at h'
  linear_combination h'

theorem exists_half (p n : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ i m : ℤ, 2 * i = 1 + (p : ℤ) ^ n * m := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two h2).pow (n := n)
  refine ⟨k + 1, 1, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℤ) hk
  push_cast at this
  rw [this]; ring

theorem cup_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (H : Subgroup (Gal p Ω)) (n c : ℕ)
  (a b lz lq : Gal p Ω → ZMod (p ^ n)) (A B A' B' : Ω),
  (∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + a h) → (∀ g ∈ H, ∀ h ∈ H, b (g * h) = b g + b h) →
  (∀ g ∈ H, ∀ h ∈ H, lz (g * h) = lz g + lz h) → (∀ g ∈ H, ∀ h ∈ H, lq (g * h) = lq g + lq h) →
  (∀ g ∈ H, g A = A ∧ g B = B ∧ g A' = A' ∧ g B' = B') →
  IsInt p ((p : Ω) ^ c * A) → IsInt p ((p : Ω) ^ c * B) → IsInt p ((p : Ω) ^ c * A') → IsInt p ((p : Ω) ^ c * B') →
  (∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → a h = a g ∧ b h = b g ∧ lz h = lz g ∧ lq h = lq g) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * A * ((lq g).val : Ω) - (p : Ω) ^ c * B * ((lz g).val : Ω)) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((b g).val : Ω) - (p : Ω) ^ c * A' * ((lq g).val : Ω) - (p : Ω) ^ c * B' * ((lz g).val : Ω)) →
  Cob2 n H (fun g h => (p : Ω) ^ (4 * c) * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ (4 * c) * (A * B' - B * A') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p hp h2 Ω _ _ H n c a b lz lq A B A' B' _ hb hz hq hfix iA iB iA' iB' hlc ⟨x, ix, hx⟩
    ⟨y, iy, hy⟩
  classical
  obtain ⟨i, m, him⟩ := exists_half p n hp.out h2
  have him' : 2 * (i : Ω) = 1 + (p : Ω) ^ n * (m : Ω) := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) him
  let R := integralClosure (O0 p) Ω
  have key : ∀ v : Ω, IsInt p v ↔ v ∈ R := fun v => Iff.rfl
  have hmap : ∀ (g : Gal p Ω) (v : Ω), v ∈ R → g v ∈ R := fun g v hv =>
    IsIntegral.map g.toAlgHom hv
  rw [key] at iA iB iA' iB' ix iy
  have iP : (p : Ω) ^ c ∈ R := pow_mem (natCast_mem R p) c
  have iN : (p : Ω) ^ n ∈ R := pow_mem (natCast_mem R p) n
  have i2 : (2 : Ω) ∈ R := ofNat_mem R 2
  refine ⟨fun k => ((p : Ω) ^ c) ^ 2 * (x * ((p : Ω) ^ c * ((b k).val : Ω))
    - ((p : Ω) ^ c * A * ((lq k).val : Ω) + (p : Ω) ^ c * B * ((lz k).val : Ω)) * k y
    - (i : Ω) * (((p : Ω) ^ c * A) * ((p : Ω) ^ c * A')) * ((lq k).val : Ω) ^ 2
    - ((p : Ω) ^ c * A) * ((p : Ω) ^ c * B') * (((lq k).val : Ω) * ((lz k).val : Ω))
    - (i : Ω) * (((p : Ω) ^ c * B) * ((p : Ω) ^ c * B')) * ((lz k).val : Ω) ^ 2), ⟨?_, ?_⟩, ?_⟩
  · intro k
    rw [key]
    have h1 := hmap k y iy
    generalize (p : Ω) ^ c * A = A₁ at *
    generalize (p : Ω) ^ c * B = B₁ at *
    generalize (p : Ω) ^ c * A' = A₂ at *
    generalize (p : Ω) ^ c * B' = B₂ at *
    generalize (p : Ω) ^ c = P at *
    repeat' first
      | assumption
      | exact natCast_mem R _
      | exact intCast_mem R _
      | apply mul_mem
      | apply sub_mem
      | apply add_mem
      | apply pow_mem
  · intro k
    obtain ⟨S, hS⟩ := hlc k
    refine ⟨insert y S, fun h hh => ⟨0, (key _).2 (zero_mem R), ?_⟩⟩
    obtain ⟨-, e1, e2, e3⟩ := hS h (fun x hx => hh x (Finset.mem_insert_of_mem hx))
    have e4 := hh y (Finset.mem_insert_self _ _)
    simp only [e1, e2, e3, e4, sub_self, mul_zero]
  · intro g hg h hh
    obtain ⟨e₁, ie₁, h₁⟩ := hx g hg
    obtain ⟨e₂, ie₂, h₂⟩ := hy h hh
    obtain ⟨fA, fB, fA', fB'⟩ := hfix g hg
    have h₂' := congrArg g h₂
    simp only [map_sub, map_mul, map_pow, map_natCast, fA', fB'] at h₂'
    obtain ⟨tb, htb⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (b g) (b h)
    obtain ⟨tq, htq⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lq g) (lq h)
    obtain ⟨tz, htz⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lz g) (lz h)
    rw [← hb g hg h hh] at htb
    rw [← hq g hg h hh] at htq
    rw [← hz g hg h hh] at htz
    have main := cup_identity _ _ _ _ _ _ _ _ _ ((b g).val : Ω) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h₁ h₂' htb htq htz him'
    refine ⟨_, ?_, Eq.trans ?_
      ((congrArg (fun t => ((p : Ω) ^ c) ^ 2 * t) main).trans (mul_left_comm _ _ _))⟩
    swap
    · simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_intCast, fA, fB, fA', fB',
        AlgEquiv.mul_apply]
      ring
    · rw [key] at ie₁ ie₂ ⊢
      have h1 := hmap g _ (hmap h y iy)
      have h3 := hmap g _ ie₂
      clear main h₁ h₂ h₂' hx hy htb htq htz him'
      generalize (p : Ω) ^ c * A = A₁ at *
      generalize (p : Ω) ^ c * B = B₁ at *
      generalize (p : Ω) ^ c * A' = A₂ at *
      generalize (p : Ω) ^ c * B' = B₂ at *
      generalize (p : Ω) ^ c = P at *
      generalize (p : Ω) ^ n = N at *
      repeat' first
        | assumption
        | exact natCast_mem R _
        | exact intCast_mem R _
        | apply mul_mem
        | apply sub_mem
        | apply add_mem
        | apply pow_mem

end GlobalTheory.CuspCup
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cochain_cup_product_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (H : Subgroup (Gal p Ω)) (n c : ℕ)
  (a b lz lq : Gal p Ω → ZMod (p ^ n)) (A B A' B' : Ω),
  (∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + a h) → (∀ g ∈ H, ∀ h ∈ H, b (g * h) = b g + b h) →
  (∀ g ∈ H, ∀ h ∈ H, lz (g * h) = lz g + lz h) → (∀ g ∈ H, ∀ h ∈ H, lq (g * h) = lq g + lq h) →
  (∀ g ∈ H, g A = A ∧ g B = B ∧ g A' = A' ∧ g B' = B') →
  IsInt p ((p : Ω) ^ c * A) → IsInt p ((p : Ω) ^ c * B) → IsInt p ((p : Ω) ^ c * A') → IsInt p ((p : Ω) ^ c * B') →
  (∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → a h = a g ∧ b h = b g ∧ lz h = lz g ∧ lq h = lq g) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * A * ((lq g).val : Ω) - (p : Ω) ^ c * B * ((lz g).val : Ω)) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((b g).val : Ω) - (p : Ω) ^ c * A' * ((lq g).val : Ω) - (p : Ω) ^ c * B' * ((lz g).val : Ω)) →
  Cob2 n H (fun g h => (p : Ω) ^ (4 * c) * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ (4 * c) * (A * B' - B * A') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  atlas_forward_decl GlobalTheory.CuspCup.cup_congruence
end

section
section
open GlobalTheory.K5 Polynomial

noncomputable section

namespace GlobalTheory.K5.KummerCup

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem map_mk_mem {n : ℕ} (f : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω) (hx : f (xn p n) ∈ S)
    (hy : f (yn p n) ∈ S) (x : On p n) : f x ∈ S := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hC : ∀ Q : Polynomial (O0 p), f (Ideal.Quotient.mk (towerIdeal p n) (C Q)) ∈ S := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add a b ha hb => rw [map_add, map_add, map_add]; exact S.add_mem ha hb
    | monomial j b =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
      refine S.mul_mem ?_ (S.pow_mem hx j)
      have e : (Ideal.Quotient.mk (towerIdeal p n)) (C (C b)) = algebraMap (O0 p) (On p n) b := rfl
      rw [e, f.commutes]
      exact S.algebraMap_mem b
  induction P using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add]; exact S.add_mem ha hb
  | monomial j Q =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    exact S.mul_mem (hC Q) (S.pow_mem hy j)

theorem pp_ne (m : ℕ) : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem q_pow (T : Tower p Ω) : ∀ m, T.qq m ^ (p ^ m) = T.qq 0
  | 0 => by simp
  | m + 1 => by rw [pow_succ', pow_mul, T.qpow, q_pow T m]

theorem qO_unit : IsUnit (qO p) := by
  have : IsUnit (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]) : Lau p) := by
    refine ⟨⟨HahnSeries.single (1 : ℤ) (1 : ℤ_[p]), HahnSeries.single (-1 : ℤ) (1 : ℤ_[p]), ?_, ?_⟩, rfl⟩
    · rw [HahnSeries.single_mul_single]; simp
    · rw [HahnSeries.single_mul_single]; simp
  exact this.map _

theorem qq_ne_zero (T : Tower p Ω) (m : ℕ) : T.qq m ≠ 0 := by
  intro h
  have h0 := q_pow T m
  rw [h, zero_pow (pp_ne m), T.q0] at h0
  exact ((qO_unit (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h0.symm

theorem zeta_mem (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [(T.prim m).pow_eq_one]
  exact isIntegral_one

theorem qq_mem (T : Tower p Ω) (m : ℕ) : T.qq m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [q_pow, T.q0]
  exact isIntegral_algebraMap

theorem zeta_sub_one_ne (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) : T.ζ n - 1 ≠ 0 :=
  sub_ne_zero.mpr ((T.prim n).ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))

theorem p_div_mem (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) :
    (p : Ω) / (T.ζ n - 1) ∈ integralClosure (O0 p) Ω := by
  classical
  have hne := zeta_sub_one_ne T hn
  have hpos : 0 < p ^ n := Nat.pos_of_ne_zero (pp_ne n)
  have h1 : eval 1 (cyclotomic (p ^ n) Ω) = (p : Ω) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact eval_one_cyclotomic_prime_pow m
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (T.prim n), eval_prod,
    ← Finset.mul_prod_erase _ _ ((mem_primitiveRoots hpos).mpr (T.prim n))] at h1
  have hR : (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) ∈
      integralClosure (O0 p) Ω := by
    refine Subalgebra.prod_mem _ fun μ hμ => ?_
    have hμ' := (mem_primitiveRoots hpos).mp (Finset.mem_of_mem_erase hμ)
    simp only [eval_sub, eval_X, eval_C]
    refine Subalgebra.sub_mem _ (Subalgebra.one_mem _) ?_
    refine IsIntegral.of_pow hpos ?_
    rw [hμ'.pow_eq_one]
    exact isIntegral_one
  generalize (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) = R at h1 hR
  simp only [eval_sub, eval_X, eval_C] at h1
  have : (p : Ω) / (T.ζ n - 1) = -R := by
    rw [div_eq_iff hne, ← h1]; ring
  rw [this]
  exact Subalgebra.neg_mem _ hR

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem fix_emb {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (x : On p n) : g (ι x) = ι x :=
  map_mk_mem ι (AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id _ _))
    (by rw [hι.1]; exact (mem_Gn.mp hg).1) (by rw [hι.2]; exact (mem_Gn.mp hg).2) x

theorem emb_mem {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) (x : On p n) :
    ι x ∈ integralClosure (O0 p) Ω :=
  map_mk_mem ι _ (by rw [hι.1]; exact zeta_mem T n) (by rw [hι.2]; exact qq_mem T n) x

theorem kum_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n) :
    a (g * h) = a g + a h := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  have h1 := ha _ ((Gn T n).mul_mem hg hh)
  rw [AlgEquiv.mul_apply, ha h hh, map_mul, map_pow, (mem_Gn.mp hg).1, ha g hg, ← mul_assoc,
    ← pow_add] at h1
  have h2 := mul_right_cancel₀ hr h1
  rw [← pow_mod_orderOf, ← (T.prim n).eq_orderOf] at h2
  have h3 := (T.prim n).pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (pp_ne n))) (ZMod.val_lt _) h2
  apply ZMod.val_injective
  rw [ZMod.val_add, ← h3, add_comm]

theorem kum_eq {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n)
    (e : h r = g r) : a h = a g := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  rw [ha g hg, ha h hh] at e
  exact ZMod.val_injective _
    ((T.prim n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (mul_right_cancel₀ hr e))

open Classical in

def ext0 {M : Type} [Zero M] (H : Subgroup (Gal p Ω)) (a : Gal p Ω → M) (g : Gal p Ω) : M :=
  if g ∈ H then a g else 0

theorem cochainExtendByZeroSubgroup_of_mem {M : Type} [Zero M] {H : Subgroup (Gal p Ω)} (a : Gal p Ω → M) {g : Gal p Ω}
    (hg : g ∈ H) : ext0 H a g = a g := if_pos hg

theorem matrixExtendByZero_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) : ∀ g ∈ Gn T n, ∀ h ∈ Gn T n,
    ext0 (Gn T n) a (g * h) = ext0 (Gn T n) a g + ext0 (Gn T n) a h := by
  intro g hg h hh
  rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a hh, cochainExtendByZeroSubgroup_of_mem a ((Gn T n).mul_mem hg hh), kum_add hr ha hg hh]

theorem cochainExtendByZero_kummer_congr_of_action {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (e1 : h (T.ζ n) = g (T.ζ n))
    (e2 : h (T.qq n) = g (T.qq n)) (e : h r = g r) : ext0 (Gn T n) a h = ext0 (Gn T n) a g := by
  have hiff : h ∈ Gn T n ↔ g ∈ Gn T n := by rw [mem_Gn, mem_Gn, e1, e2]
  by_cases hg : g ∈ Gn T n
  · rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a (hiff.mpr hg), kum_eq hr ha hg (hiff.mpr hg) e]
  · unfold ext0
    rw [if_neg hg, if_neg (fun hh => hg (hiff.mp hh))]

theorem kummerTower_coboundaryOne_prime_smul {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Ω} (hf : Cob1 k H f)
    (e : ∀ g ∈ H, f' g = (p : Ω) * f g) : Cob1 k H f' := by
  obtain ⟨x, hx, h⟩ := hf
  have hp : IsIntegral (O0 p) (p : Ω) := (integralClosure (O0 p) Ω).natCast_mem p
  refine ⟨(p : Ω) * x, hp.mul hx, fun g hg => ?_⟩
  obtain ⟨z, hz, hz'⟩ := h g hg
  refine ⟨(p : Ω) * z, hp.mul hz, ?_⟩
  rw [e g hg, map_mul, map_natCast]
  linear_combination (p : Ω) * hz'

theorem kummerTower_coboundaryTwo_congr {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Gal p Ω → Ω} (hf : Cob2 k H f)
    (e : ∀ g ∈ H, ∀ h ∈ H, f' g h = f g h) : Cob2 k H f' := by
  obtain ⟨w, hw, h⟩ := hf
  exact ⟨w, hw, fun g hg g' hg' => (e g hg g' hg') ▸ h g hg g' hg'⟩

theorem root_ne_zero {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) (ι : On p n →ₐ[O0 p] Ω) {k : ℤ}
    {w : (On p n)ˣ} {r : Ω} (hr : r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w) : r ≠ 0 := by
  rintro rfl
  rw [zero_pow (pp_ne n)] at hr
  exact mul_ne_zero (zpow_ne_zero k (zeta_sub_one_ne T hn)) (w.isUnit.map ι).ne_zero hr.symm

theorem coef_int {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (k : ℤ) (β : On p n) :
    IsInt p ((p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  have e : (p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) =
      (p : Ω) ^ (c + 1) * ι β + (p : Ω) ^ c * (k : Ω) * T.ζ n * ((p : Ω) / (T.ζ n - 1)) := by ring
  rw [e]
  exact add_mem (mul_mem (pow_mem hp _) (emb_mem hι β))
    (mul_mem (mul_mem (mul_mem (pow_mem hp _) (intCast_mem _ k)) (zeta_mem T n)) (p_div_mem T hn))

theorem coef_int' {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (α : On p n) : IsInt p ((p : Ω) ^ c * ι α) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  exact mul_mem (pow_mem hp _) (emb_mem hι α)

theorem coef_fix {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (k : ℤ) (β : On p n) :
    g (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) = ι β + (k : Ω) * T.ζ n / (T.ζ n - 1) := by
  rw [map_add, map_div₀, map_mul, map_sub, map_one, map_intCast, fix_emb hι hg, (mem_Gn.mp hg).1]

theorem cup_kummer_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k l : ℤ) (w w' : (On p n)ˣ) (α β α' β' : On p n), IsDlog p n (w : On p n) α β → IsDlog p n (w' : On p n) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w → s ^ (p ^ n) = (T.ζ n - 1) ^ l * ι w' →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a → IsKum T n (Gn T n) s b →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob2 n (Gn T n) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ c * (ι (fPi p n k l α β α' β') / (T.ζ n - 1)) * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummerCochain_eq_dlog_combination_finiteLevel p hp2
  refine ⟨4 * (c + 1), ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k l w w' α β α' β' hw hw' r s hr hs a b lz lq ha hb hz hq
  have r0 := root_ne_zero hn ι hr
  have s0 := root_ne_zero hn ι hs
  have z0 : T.ζ (2 * n) ≠ 0 := (T.prim (2 * n)).ne_zero (pp_ne _)
  have q0 := qq_ne_zero T (2 * n)
  have h1 := hc Ω hΩ T n hn ι hι k w α β hw r hr a lz lq ha hz hq
  have h2 := hc Ω hΩ T n hn ι hι l w' α' β' hw' s hs b lz lq hb hz hq
  have key := GlobalTheory.T.kummer_cochain_cup_product_congruence p hp2 Ω (Gn T n) n (c + 1) (ext0 (Gn T n) a) (ext0 (Gn T n) b)
    (ext0 (Gn T n) lz) (ext0 (Gn T n) lq) (ι α) (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))
    (ι α') (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1))
    (matrixExtendByZero_add r0 ha) (matrixExtendByZero_add s0 hb) (matrixExtendByZero_add z0 hz) (matrixExtendByZero_add q0 hq)
    (fun g hg => ⟨fix_emb hι hg _, coef_fix hι hg _ _, fix_emb hι hg _, coef_fix hι hg _ _⟩)
    (coef_int' hι _ _) (coef_int hn hι _ _ _) (coef_int' hι _ _) (coef_int hn hι _ _ _)
    (fun g => ⟨{T.ζ n, T.qq n, r, s, T.ζ (2 * n), T.qq (2 * n)}, fun h hS =>
      ⟨cochainExtendByZero_kummer_congr_of_action r0 ha (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action s0 hb (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action z0 hz (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action q0 hq (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp))⟩⟩)
    (kummerTower_coboundaryOne_prime_smul h1 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
    (kummerTower_coboundaryOne_prime_smul h2 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
  refine kummerTower_coboundaryTwo_congr key fun g hg h hh => ?_
  have hne := zeta_sub_one_ne T hn
  have e : ι (fPi p n k l α β α' β') / (T.ζ n - 1) =
      ι α * (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1)) - (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ι α' := by
    simp only [fPi, map_sub, map_mul, map_add, map_intCast, map_one, hι.1]
    field_simp
    ring
  simp only [cochainExtendByZeroSubgroup_of_mem _ hg, cochainExtendByZeroSubgroup_of_mem _ hh, e]

end GlobalTheory.K5.KummerCup
end
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k l : ℤ) (w w' : (On p n)ˣ) (α β α' β' : On p n), IsDlog p n (w : On p n) α β → IsDlog p n (w' : On p n) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w → s ^ (p ^ n) = (T.ζ n - 1) ^ l * ι w' →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a → IsKum T n (Gn T n) s b →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob2 n (Gn T n) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ c * (ι (fPi p n k l α β α' β') / (T.ζ n - 1)) * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  atlas_forward_decl GlobalTheory.K5.KummerCup.cup_kummer_dlog
end

section
section
noncomputable section

namespace GlobalTheory.K5.LevelDown

open Polynomial GlobalTheory.K5 GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_adjoin (L : ℕ) (x : On p L) : x ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  set S := Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hb : ∀ b : O0 p, Ideal.Quotient.mk (towerIdeal p L) (C (C b)) ∈ S := by
    intro b
    have : Ideal.Quotient.mk (towerIdeal p L) (C (C b)) = algebraMap (O0 p) (On p L) b := by
      first | rfl | simp [Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_apply]
    rw [this]; exact S.algebraMap_mem b
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p L) (C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hb b
    | add f g hf hg => rw [C_add, map_add]; exact S.add_mem hf hg
    | monomial k b _ =>
      rw [C_mul, C_pow, map_mul, map_pow]
      exact S.mul_mem (hb b) (S.pow_mem hx _)
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
  | monomial k a _ => rw [map_mul, map_pow]; exact S.mul_mem (hC a) (S.pow_mem hy _)

theorem zeta_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem isInt_nat (m : ℕ) : IsInt p (m : Ω) := by
  rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω)]; exact isIntegral_algebraMap

theorem isInt_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (x : On p L) : IsInt p (ι x) := by
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ (integralClosure (O0 p) Ω).comap ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show ι (xn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.1]
      exact IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [(T.prim L).pow_eq_one]; exact isIntegral_one)
    · show ι (yn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.2]
      refine IsIntegral.of_pow (pow_pos hp.out.pos L) ?_
      rw [qq_pow]; exact isIntegral_algebraMap
  exact h (mem_adjoin L x)

theorem fix_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (g : Gal p Ω) (hg : g ∈ Gn T L) (x : On p L) : g (ι x) = ι x := by
  have hg' := (mem_gn T L g).1 hg
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤
      AlgHom.equalizer ((g : Ω →ₐ[O0 p] Ω).comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show g (ι (xn p L)) = ι (xn p L)
      rw [hι.1]; exact hg'.1
    · show g (ι (yn p L)) = ι (yn p L)
      rw [hι.2]; exact hg'.2
  exact h (mem_adjoin L x)

theorem cong_mono {k m : ℕ} (h : k ≤ m) {x y : Ω} (hc : Cong p m x y) : Cong p k x y := by
  obtain ⟨z, hz, e⟩ := hc
  refine ⟨(p : Ω) ^ (m - k) * z, IsIntegral.mul (IsIntegral.pow (isInt_nat p) _) hz, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem locallyConstantModPrimePow_of_le {k m : ℕ} (h : k ≤ m) {w : Gal p Ω → Ω} (hw : LocallyConstantOneCochain m w) : LocallyConstantOneCochain k w :=
  ⟨hw.1, fun g => by
    obtain ⟨S, hS⟩ := hw.2 g
    exact ⟨S, fun h' hh => cong_mono h (hS h' hh)⟩⟩

theorem cong_mul' {k : ℕ} {x y x' y' : Ω} (h : Cong p k x y) (h' : Cong p k x' y')
    (hx' : IsInt p x') (hy : IsInt p y) : Cong p k (x * x') (y * y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a * x' + y * b, (ha.mul hx').add (hy.mul hb), by linear_combination x' * e + y * e'⟩

theorem kum_down (T : GlobalTheory.K5.Tower p Ω) {n L : ℕ} (hnL : n ≤ L) {H : Subgroup (Gal p Ω)} {R : Ω}
    (hR : R ≠ 0) {aL : Gal p Ω → ZMod (p ^ L)} (haL : IsKum T L H R aL)
    {a : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H (R ^ p ^ (L - n)) a) {g : Gal p Ω}
    (hg : g ∈ H) : (a g).val ≡ (aL g).val [MOD p ^ n] := by
  have e1 := ha g hg
  rw [map_pow, haL g hg, mul_pow, ← pow_mul, mul_comm ((aL g).val), pow_mul] at e1
  have hz : T.ζ L ^ p ^ (L - n) = T.ζ n := by
    have := zeta_pow_sub T n (L - n); rwa [Nat.add_sub_cancel' hnL] at this
  rw [hz] at e1
  have e2 := mul_right_cancel₀ (pow_ne_zero _ hR) e1
  exact ((zeta_pow_eq_iff T n _ _).1 e2).symm

end GlobalTheory.K5.LevelDown

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.hodgeTate_cup_kummer_classes_eq_dlog_determinant p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ hclo T L n hnL hn ι hι u v α β α' β' hu hv r s hr hs a b lz lq ha hb hlz hlq
  haveI := hclo.clo
  have hpr : p.Prime := Fact.out
  have hL : 1 ≤ L := le_trans hn hnL
  have hpos : ∀ k, 0 < p ^ k := fun k => pow_pos hpr.pos k
  have hunit : ∀ w : (On p L)ˣ, ι (w : On p L) ≠ 0 := fun w h => by
    have := congrArg ι w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hroot : ∀ (w : (On p L)ˣ) (x : Ω), x ^ p ^ n = ι (w : On p L) → ∃ X : Ω, X ≠ 0 ∧
      X ^ p ^ (L - n) = x ∧ X ^ p ^ L = (T.ζ L - 1) ^ (0 : ℤ) * ι (w : On p L) := by
    intro w x hx
    obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (hpos (L - n))
    refine ⟨X, ?_, hX, ?_⟩
    · rintro rfl
      rw [zero_pow (pow_ne_zero _ hpr.ne_zero)] at hX
      rw [← hX, zero_pow (pow_ne_zero _ hpr.ne_zero)] at hx
      exact hunit w hx.symm
    · rw [zpow_zero, one_mul, ← hx, ← hX, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnL]
  obtain ⟨R, hR0, hR, hRL⟩ := hroot u r hr
  obtain ⟨S, hS0, hS, hSL⟩ := hroot v s hs
  have hfix := LevelDown.fix_emb T L ι hι
  have hgn := fun g (hg : g ∈ Gn T L) => (Basic.mem_gn T L g).1 hg
  obtain ⟨aL, haL⟩ := Basic.exists_isKum T L (Gn T L) hR0 (fun g hg => by
    rw [hRL, zpow_zero, one_mul]; exact hfix g hg _)
  obtain ⟨bL, hbL⟩ := Basic.exists_isKum T L (Gn T L) hS0 (fun g hg => by
    rw [hSL, zpow_zero, one_mul]; exact hfix g hg _)
  have hZ0 : T.ζ (2 * L) ≠ 0 := (T.prim _).ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hZL : T.ζ (2 * L) ^ p ^ L = T.ζ L := by
    rw [two_mul]; exact LevelDown.zeta_pow_sub T L L
  have hQL : T.qq (2 * L) ^ p ^ L = T.qq L := by
    rw [two_mul]; exact LevelDown.qq_pow_sub T L L
  obtain ⟨zL, hzL⟩ := Basic.exists_isKum T L (Gn T L) hZ0 (fun g hg => by
    rw [hZL]; exact (hgn g hg).1)
  obtain ⟨qL, hqL⟩ := Basic.exists_isKum T L (Gn T L) (Basic.qq_ne_zero T _) (fun g hg => by
    rw [hQL]; exact (hgn g hg).2)
  obtain ⟨w, hw, hcong⟩ := hc Ω hclo T L hL ι hι 0 0 u v α β α' β' hu hv R S hRL hSL aL bL zL qL
    haL hbL hzL hqL
  have e2 : L + n + (L - n) = 2 * L := by omega
  have hZn : T.ζ (2 * L) ^ p ^ (L - n) = T.ζ (L + n) := by
    rw [← e2]; exact LevelDown.zeta_pow_sub T (L + n) (L - n)
  have hQn : T.qq (2 * L) ^ p ^ (L - n) = T.qq (L + n) := by
    rw [← e2]; exact LevelDown.qq_pow_sub T (L + n) (L - n)
  have hX : ι (fPi p L 0 0 α β α' β') / (T.ζ L - 1) = ι (α * β' - β * α') := by
    have hne : T.ζ L - 1 ≠ 0 :=
      sub_ne_zero.2 ((T.prim L).ne_one (Nat.one_lt_pow (by omega) hpr.one_lt))
    rw [div_eq_iff hne]
    have : fPi p L 0 0 α β α' β' = (xn p L - 1) * (α * β' - β * α') := by
      simp only [fPi]; push_cast; ring
    rw [this, map_mul, map_sub, hι.1, map_one]; ring
  refine ⟨w, LevelDown.locallyConstantModPrimePow_of_le hnL hw, fun g hg h hh => ?_⟩
  refine Basic.cong_trans ?_ (LevelDown.cong_mono hnL (hcong g hg h hh))
  beta_reduce
  rw [hX]
  have hA : Cong p n ((a g).val : Ω) ((aL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hR0 haL (by rw [hR]; exact ha) hg)
  have hB : Cong p n ((b h).val : Ω) ((bL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hS0 hbL (by rw [hS]; exact hb) hh)
  have hC : Cong p n ((lz g).val : Ω) ((zL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hZ0 hzL (by rw [hZn]; exact hlz) hg)
  have hD : Cong p n ((lq h).val : Ω) ((qL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL (Basic.qq_ne_zero T _) hqL (by rw [hQn]; exact hlq) hh)
  have iN := fun m : ℕ => (LevelDown.isInt_nat (p := p) (Ω := Ω) m)
  have iP : IsInt p ((p : Ω) ^ c) := IsIntegral.pow (iN p) c
  have iX : IsInt p (ι (α * β' - β * α')) := LevelDown.isInt_emb T L ι hι _
  refine Basic.cong_add ?_ ?_
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hA hB (iN _) (iN _)) ((iN _).mul (iN _)) iP
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hC hD (iN _) (iN _)) ((iN _).mul (iN _)) (iP.mul iX)
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  atlas_forward_decl GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reparametrizationByTowerParameter : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∃ ψ : O0 p →+* Ω, IsReb T n ψ := by
  first | exact @GlobalTheory.Glue.exists_isReb | exact GlobalTheory.Glue.exists_isReb | (intros; apply GlobalTheory.Glue.exists_isReb <;> assumption)
end

section
section
noncomputable section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois Polynomial

namespace GlobalTheory.K5.Reb

def RebT {p : ℕ} [Fact p.Prime] (Ω : Type) [Field Ω] (_ψ : O0 p →+* Ω) : Type := Ω

section Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω]

instance (ψ : O0 p →+* Ω) : Field (RebT Ω ψ) := inferInstanceAs (Field Ω)

instance (ψ : O0 p →+* Ω) : Algebra (O0 p) (RebT Ω ψ) := ψ.toAlgebra

end Inst

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {T : GlobalTheory.K5.Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω}

theorem mem_range (hψ : IsReb T L ψ) (a : O0 p) : ∃ b, ψ b = algebraMap (O0 p) Ω a := by
  have h : algebraMap (O0 p) Ω a ∈ ψ.range := by
    rw [hψ.rng, Subalgebra.mem_toSubring]
    exact Subalgebra.algebraMap_mem _ a
  exact RingHom.mem_range.1 h

def jf (hψ : IsReb T L ψ) (a : O0 p) : O0 p := (mem_range hψ a).choose

theorem jf_spec (hψ : IsReb T L ψ) (a : O0 p) : ψ (jf hψ a) = algebraMap (O0 p) Ω a :=
  (mem_range hψ a).choose_spec

def jj (hψ : IsReb T L ψ) : O0 p →+* O0 p where
  toFun := jf hψ
  map_one' := hψ.inj (by rw [jf_spec, map_one, map_one])
  map_mul' a b := hψ.inj (by rw [jf_spec, map_mul, map_mul, jf_spec, jf_spec])
  map_zero' := hψ.inj (by rw [jf_spec, map_zero, map_zero])
  map_add' a b := hψ.inj (by rw [jf_spec, map_add, map_add, jf_spec, jf_spec])

theorem comp_jj (hψ : IsReb T L ψ) : ψ.comp (jj hψ) = algebraMap (O0 p) Ω :=
  RingHom.ext (jf_spec hψ)

theorem isInt_iff (hψ : IsReb T L ψ) (x : Ω) : @IsInt p _ (RebT Ω ψ) _ _ x ↔ IsInt p x := by
  constructor
  · rintro ⟨f, hf, h⟩
    let A := Algebra.adjoin (O0 p) {T.qq L}
    have hq : IsIntegral (O0 p) (T.qq L) := by
      refine ⟨X ^ (p ^ L) - C (qO p), monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ?_⟩
      rw [← aeval_def]
      simp [GlobalTheory.K5.Basic.qq_pow]
    haveI : Algebra.IsIntegral (O0 p) A := Algebra.IsIntegral.adjoin (by rintro _ rfl; exact hq)
    let g : O0 p →+* A := ψ.codRestrict A (fun b => by
      have := ψ.mem_range_self b
      rw [hψ.rng] at this
      exact this)
    have hA : IsIntegral A x := by
      refine ⟨f.map g, hf.map g, ?_⟩
      rw [eval₂_map]
      have e : (algebraMap A Ω).comp g = ψ := RingHom.ext fun _ => rfl
      rw [e]
      exact h
    exact isIntegral_trans x hA
  · rintro ⟨f, hf, h⟩
    refine ⟨f.map (jj hψ), hf.map _, ?_⟩
    show eval₂ ψ x (f.map (jj hψ)) = 0
    rw [eval₂_map]
    rw [comp_jj]
    exact h

theorem cong_iff (hψ : IsReb T L ψ) (k : ℕ) (x y : Ω) :
    @Cong p _ (RebT Ω ψ) _ _ k x y ↔ Cong p k x y := by
  constructor
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).1 hz, e⟩
  · rintro ⟨z, hz, e⟩
    exact ⟨z, (isInt_iff hψ z).2 hz, e⟩

theorem isClo (hΩ : IsClo p Ω) (hψ : IsReb T L ψ) : IsClo p (RebT Ω ψ) where
  inj := hψ.inj
  alg := by
    refine ⟨fun (x : Ω) => ?_⟩
    obtain ⟨f, hf, h⟩ := hΩ.alg.isAlgebraic x
    have hinj : Function.Injective (jj hψ) := by
      intro a b hab
      apply hΩ.inj
      rw [← comp_jj hψ, RingHom.comp_apply, RingHom.comp_apply, hab]
    refine ⟨f.map (jj hψ), (Polynomial.map_ne_zero_iff hinj).2 hf, ?_⟩
    show eval₂ ψ x (f.map (jj hψ)) = 0
    rw [eval₂_map, comp_jj, ← aeval_def]
    exact h
  clo := hΩ.clo

theorem zp_eq (hψ : IsReb T L ψ) (z : ℤ_[p]) :
    ψ (algebraMap ℤ_[p] (O0 p) z) = algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) := by
  have e : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.C z) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
    congr 1
    show HahnSeries.ofPowerSeries ℤ ℤ_[p] (algebraMap ℤ_[p] (PowerSeries ℤ_[p]) z) = _
    rw [← HahnSeries.ofPowerSeries_C]
    rfl
  rw [e]
  have hp0 : (p : ℤ) ^ L ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
  · by_cases hi : i = 0
    · subst hi; simp [HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ L * i ≠ 0 := mul_ne_zero hp0 hi
      simp [HahnSeries.C_apply, HahnSeries.coeff_single, hi, this]
  · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem isAlgZp_iff (hψ : IsReb T L ψ) (x : Ω) : @IsAlgZp p _ (RebT Ω ψ) _ _ x ↔ IsAlgZp p x := by
  have hc : ψ.comp (algebraMap ℤ_[p] (O0 p)) = (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) :=
    RingHom.ext (zp_eq hψ)
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    have h' : eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0 := h
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def] at h'
    exact h'
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_⟩
    show eval₂ ψ x (P.map (algebraMap ℤ_[p] (O0 p))) = 0
    rw [eval₂_map, hc, ← eval₂_map, ← aeval_def]
    exact h

def tw (hψ : IsReb T L ψ) : GlobalTheory.K5.Tower p (RebT Ω ψ) where
  ζ := T.ζ
  qq k := T.qq (L + k)
  prim := T.prim
  ζpow := T.ζpow
  q0 := hψ.par.symm
  qpow k := T.qpow (L + k)

def down (hψ : IsReb T L ψ) (g : Gal p (RebT Ω ψ)) : Gal p Ω :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : Ω ≃+* Ω)) (fun a => by
    obtain ⟨b, hb⟩ := mem_range hψ a
    rw [← hb]
    exact g.commutes b)

theorem down_mul (hψ : IsReb T L ψ) (g h : Gal p (RebT Ω ψ)) : down hψ (g * h) = down hψ g * down hψ h :=
  AlgEquiv.ext fun _ => rfl

theorem fix_range (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) (a : O0 p) : g (ψ a) = ψ a := by
  have h1 : ψ a ∈ (Algebra.adjoin (O0 p) {T.qq L}).toSubring := hψ.rng ▸ ψ.mem_range_self a
  have h2 : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by rintro x rfl; exact hg)
  exact (AlgHom.mem_equalizer _ _ _).1 (h2 h1)

def up (hψ : IsReb T L ψ) (g : Gal p Ω) (hg : g (T.qq L) = T.qq L) : Gal p (RebT Ω ψ) :=
  AlgEquiv.ofRingEquiv (f := (g.toRingEquiv : RebT Ω ψ ≃+* RebT Ω ψ)) (fun a => fix_range hψ g hg a)

theorem isAlgZp_zeta (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) : IsAlgZp p (T.ζ L) := by
  refine ⟨X ^ (p ^ L) - C 1, (monic_X_pow_sub_C _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).ne_zero, ?_⟩
  simp [(T.prim L).pow_eq_one]

theorem mem_H (hψ : IsReb T L ψ) {g : Gal p (RebT Ω ψ)} (hg : g ∈ Ggeo p (RebT Ω ψ)) :
    down hψ g ∈ Ggeo p Ω ⊓ Gn T L := by
  have hgeo : down hψ g ∈ Ggeo p Ω := fun x hx => hg x ((isAlgZp_iff hψ x).2 hx)
  refine Subgroup.mem_inf.2 ⟨hgeo, (GlobalTheory.K5.Basic.mem_gn T L _).2 ⟨hgeo _ (isAlgZp_zeta T L), ?_⟩⟩
  have h : g (ψ (qO p)) = ψ (qO p) := g.commutes (qO p)
  rw [hψ.par] at h
  exact h

theorem exists_up (hψ : IsReb T L ψ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    ∃ g' : Gal p (RebT Ω ψ), g' ∈ Ggeo p (RebT Ω ψ) ∧ down hψ g' = g := by
  have hg1 := (Subgroup.mem_inf.1 hg).1
  have hq := ((GlobalTheory.K5.Basic.mem_gn T L g).1 (Subgroup.mem_inf.1 hg).2).2
  exact ⟨up hψ g hq, fun x hx => hg1 x ((isAlgZp_iff hψ x).1 hx), AlgEquiv.ext fun _ => rfl⟩

theorem h1_geometric_level_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong p n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong p n ((p : Ω) ^ c * o) 0) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummer_cocycle_twisted_coboundary p hp2
  refine ⟨c, fun Ω _ _ hΩ T L n _ lq hlq => ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_reparametrizationByTowerParameter p Ω hΩ T L
  have hk : IsKum (tw hψ) n (Ggeo p (RebT Ω ψ)) ((tw hψ).qq n) (fun g => lq (down hψ g)) :=
    fun g hg => hlq (down hψ g) (mem_H hψ hg)
  obtain ⟨h1, h2⟩ := hc (RebT Ω ψ) (isClo hΩ hψ) (tw hψ) n (fun _ => 0) _ hk
  constructor
  · intro a ha hcoc
    have hlc : IntegralLocallyConstCochainModPow n (Ggeo p (RebT Ω ψ)) (fun g => a (down hψ g)) := by
      refine ⟨fun g hg => (isInt_iff hψ _).2 (ha.1 _ (mem_H hψ hg)), fun g hg => ?_⟩
      obtain ⟨S, hS⟩ := ha.2 _ (mem_H hψ hg)
      exact ⟨S, fun h hh hx => (cong_iff hψ n _ _).2 (hS _ (mem_H hψ hh) hx)⟩
    have hco : IsTwistedOneCocycle 0 n (Ggeo p (RebT Ω ψ)) (fun _ => 0) (fun g => a (down hψ g)) := by
      intro g hg h hh
      simp only [pow_zero, one_mul]
      rw [down_mul]
      exact (cong_iff hψ n _ _).2 (hcoc _ (mem_H hψ hg) _ (mem_H hψ hh))
    obtain ⟨o, ho, hof, x, hx, hxc⟩ := h1 _ hlc hco
    refine ⟨o, (isInt_iff hψ o).1 ho, fun g hg => ?_, x, (isInt_iff hψ x).1 hx, fun g hg => ?_⟩
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      exact hof g' hg'
    · obtain ⟨g', hg', rfl⟩ := exists_up hψ hg
      have e := hxc g' hg'
      rw [pow_zero, one_mul] at e
      exact (cong_iff hψ n _ _).1 e
  · intro o ho hof hcob
    obtain ⟨x, hx, hxc⟩ := hcob
    refine (cong_iff hψ n _ _).1 (h2 o ((isInt_iff hψ o).2 ho) (fun g hg => hof _ (mem_H hψ hg))
      ⟨x, (isInt_iff hψ x).2 hx, fun g hg => ?_⟩)
    rw [pow_zero, one_mul]
    exact (cong_iff hψ n _ _).2 (hxc _ (mem_H hψ hg))

end GlobalTheory.K5.Reb
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_level_h1_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong p n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong p n ((p : Ω) ^ c * o) 0) := by
  atlas_forward_decl GlobalTheory.K5.Reb.h1_geometric_level_coboundary
end

section
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zcong (n : ℕ) (A B : ℤ) (h : (A : ZMod (p ^ n)) = B) : Cong p n (A : Ω) (B : Ω) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨((-k : ℤ) : Ω), isInt_intCast _, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hk
  push_cast at this ⊢
  linear_combination -this

theorem isInt_natCast (m : ℕ) : IsInt p (m : Ω) := by
  have := isInt_intCast (p := p) (Ω := Ω) (m : ℤ)
  simpa using this

theorem isInt_pow_p (c : ℕ) : IsInt p ((p : Ω) ^ c) := by
  have := isInt_natCast (p := p) (Ω := Ω) (p ^ c)
  simpa using this

theorem conj_invariant {G M : Type*} [Group G] [AddCommGroup M] (H : Subgroup G) (φ : G → M)
    (hφ : ∀ g ∈ H, ∀ h ∈ H, φ (g * h) = φ g + φ h) {σ h : G} (hσ : σ ∈ H) (hh : h ∈ H) :
    φ (σ * h * σ⁻¹) = φ h := by
  have h1 : φ 1 = 0 := by
    have e := hφ 1 H.one_mem 1 H.one_mem
    rw [mul_one] at e
    have e' : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero, ← e]
    exact add_left_cancel e'
  have h2 : φ σ + φ σ⁻¹ = 0 := by
    rw [← hφ σ hσ σ⁻¹ (H.inv_mem hσ), mul_inv_cancel, h1]
  rw [hφ _ (H.mul_mem hσ hh) _ (H.inv_mem hσ), hφ σ hσ h hh, add_right_comm, h2, zero_add]

theorem zeta_eq_pow (T : Tower p Ω) (m k : ℕ) : T.ζ m = T.ζ (m + k) ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    show _ = T.ζ (m + k + 1) ^ p ^ (k + 1)
    rw [ih, ← T.ζpow (m + k), ← pow_mul, ← pow_succ']

theorem gn_fix_zeta (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [zeta_eq_pow T n k, map_pow, ((mem_gn T _ g).1 hg).1]

theorem kum_add (T : Tower p Ω) {L n : ℕ} (hn : n ≤ L) {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T L) r a) : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, a (g * h) = a g + a h := by
  intro g hg h hh
  obtain ⟨χ, hχ⟩ := exists_isCyc T n
  have h1 : χ g = 1 := (isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T hn hg)
  rw [isKum_mul hχ hr ha hg hh, h1, one_mul]

theorem isAlgZp_zeta (T : Tower p Ω) (m : ℕ) : IsAlgZp p (T.ζ m) := by
  refine ⟨Polynomial.X ^ (p ^ m) - Polynomial.C 1,
    Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos m) 1, ?_⟩
  simp [(T.prim m).pow_eq_one]

theorem kum_geo_zero (T : Tower p Ω) {n m : ℕ} {H : Subgroup (Gal p Ω)} {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H (T.ζ m) a) {g : Gal p Ω} (hH : g ∈ H) (hg : g ∈ Ggeo p Ω) : a g = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hg' : ∀ x : Ω, IsAlgZp p x → g x = x := hg
  have e := ha g hH
  rw [hg' _ (isAlgZp_zeta T m)] at e
  have hz : T.ζ m ≠ 0 := (T.prim m).ne_zero (pow_ne_zero _ hp.out.ne_zero)
  have e1 : T.ζ n ^ (a g).val = 1 := mul_right_cancel₀ hz (by rw [one_mul]; exact e.symm)
  have e2 : T.ζ n ^ (a g).val = T.ζ n ^ (0 : ℕ) := by rw [pow_zero]; exact e1
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e2
  simpa using e2

theorem conj_mem_ggeo {σ h : Gal p Ω} (hh : h ∈ Ggeo p Ω) : σ * h * σ⁻¹ ∈ Ggeo p Ω := by
  have hh' : ∀ x : Ω, IsAlgZp p x → h x = x := hh
  show ∀ x : Ω, IsAlgZp p x → (σ * h * σ⁻¹) x = x
  rintro x ⟨P, hP, hPx⟩
  have hx' : IsAlgZp p (σ⁻¹ x) := ⟨P, hP, by
    have := Polynomial.aeval_algHom_apply (σ⁻¹ : Gal p Ω).toAlgHom x (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [hPx, map_zero] at this
    exact this⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh' _ hx', ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

end GlobalTheory.EdgeAlg

namespace GlobalTheory.EdgeAlg

open GlobalTheory.K5.Basic

theorem edge_class_cup : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt p f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  classical
  intro p _ hp2 c₁
  obtain ⟨c', hc'⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₁ + c', ?_⟩
  intro Ω _ _ hclo T L n hnL x y lz lq η f hxy hlz hlq hfi hff hη hηlc hcob
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨W, ⟨hWi, hWlc⟩, hW⟩ := hcob
  have hx_add : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h := fun g hg h hh => (hxy g hg h hh).1
  have hlq_add := kum_add T hnL (qq_ne_zero T (L + n)) hlq
  have hlz0 : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), lz g = 0 := fun g hg =>
    kum_geo_zero T hlz (Subgroup.mem_inf.1 hg).2 (Subgroup.mem_inf.1 hg).1
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  let a : Gal p Ω → Ω := fun g => (p : Ω) ^ c₁ * ((η g).val : Ω) - W g
  have haLC : IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a := by
    refine ⟨fun g _ => IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) (isInt_natCast _)) (hWi g), fun g hg => ?_⟩
    obtain ⟨S1, hS1⟩ := hηlc g hg
    obtain ⟨S2, hS2⟩ := hWlc g
    refine ⟨S1 ∪ S2, fun h hh hS => ?_⟩
    have e1 := hS1 h hh (fun z hz => hS z (Finset.mem_union_left _ hz))
    have e2 := hS2 h (fun z hz => hS z (Finset.mem_union_right _ hz))
    simp only [a, e1]
    exact cong_sub (cong_refl _ _) e2
  have haCoc : ∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong p n (a (g * h)) (a g + g (a h)) := by
    intro g hg h hh
    have hgG := (Subgroup.mem_inf.1 hg).2
    have hhG := (Subgroup.mem_inf.1 hh).2
    obtain ⟨w, hw, ew⟩ := hW g hgG h hhG
    obtain ⟨u, hu, eu⟩ := zcong (p := p) (Ω := Ω) n (((x g).val : ℤ) * ((y h).val : ℤ))
      (((η h).val : ℤ) - ((η (g * h)).val : ℤ) + ((η g).val : ℤ)) (by
        simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
        exact hη g hg h hh)
    simp only [hlz0 g hg, ZMod.val_zero, Nat.cast_zero] at ew
    refine ⟨(p : Ω) ^ c₁ * u - w, IsIntegral.sub (IsIntegral.mul (isInt_pow_p c₁) hu) hw, ?_⟩
    simp only [a, map_sub, map_mul, map_pow, map_natCast]
    push_cast at eu
    linear_combination (p : Ω) ^ c₁ * eu - ew
  obtain ⟨o, hoi, hofix, z, hzi, hz⟩ := (hc' Ω hclo T L n hnL lq hlqΔ).1 a haLC haCoc
  refine ⟨o, hoi, hofix, fun σ hσ => ?_⟩
  have hsi : ∀ v : Ω, σ⁻¹ (σ v) = v := fun v => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hfs : σ⁻¹ f = f := hff _ ((Gn T L).inv_mem hσ)
  refine ⟨σ⁻¹ (z - σ z - (p : Ω) ^ c' * W σ),
    isInt_gal _ (IsIntegral.sub (IsIntegral.sub hzi (isInt_gal σ hzi)) (IsIntegral.mul (isInt_pow_p c') (hWi σ))),
    fun h hh => ?_⟩
  have hhG := (Subgroup.mem_inf.1 hh).2
  have hh2 : σ * h * σ⁻¹ ∈ (Ggeo p Ω ⊓ Gn T L) := Subgroup.mem_inf.2
    ⟨conj_mem_ggeo (Subgroup.mem_inf.1 hh).1, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hhG) ((Gn T L).inv_mem hσ)⟩
  have hh2G := (Subgroup.mem_inf.1 hh2).2
  have hcomm : σ * h * σ⁻¹ * σ = σ * h := by group
  have hxh2 : x (σ * h * σ⁻¹) = x h := conj_invariant (Gn T L) x hx_add hσ hhG
  have hlqh2 : lq (σ * h * σ⁻¹) = lq h := conj_invariant (Gn T L) lq hlq_add hσ hhG
  have hlzh2 : lz (σ * h * σ⁻¹) = 0 := hlz0 _ hh2
  have hsh : σ (h z) = (σ * h * σ⁻¹) (σ z) := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  have hs2 : ∀ v : Ω, σ⁻¹ ((σ * h * σ⁻¹) v) = h (σ⁻¹ v) := fun v => by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hsi]
  obtain ⟨w1, hw1, e1⟩ := hW _ hh2G σ hσ
  obtain ⟨w2, hw2, e2⟩ := hW σ hσ h hhG
  obtain ⟨w3, hw3, e3⟩ := hz h hh
  obtain ⟨w4, hw4, e4⟩ := hz _ hh2
  obtain ⟨u0, hu0, e0⟩ := zcong (p := p) (Ω := Ω) n
    (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : ℤ)
    (((η (σ * h * σ⁻¹)).val : ℤ) - ((η h).val : ℤ) - ((x h).val : ℤ) * ((y σ).val : ℤ) + ((x σ).val : ℤ) * ((y h).val : ℤ))
    (by simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val])
  push_cast at e0
  simp only [hxh2, hlzh2, hcomm, ZMod.val_zero, Nat.cast_zero] at e1
  simp only [a, hlqh2] at e3 e4
  have e3s := congrArg σ e3
  simp only [map_sub, map_mul, map_pow, map_natCast, hsh] at e3s
  have K : (p : Ω) ^ c₁ * (p : Ω) ^ c' * (((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : ℕ) : Ω)
      - (o - σ o - (p : Ω) ^ c₁ * (p : Ω) ^ c' * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)
      - (((σ * h * σ⁻¹) z - (σ * h * σ⁻¹) (σ z) - (p : Ω) ^ c' * (σ * h * σ⁻¹) (W σ)) - (z - σ z - (p : Ω) ^ c' * W σ))
      = (p : Ω) ^ n * ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3) := by
    linear_combination (p : Ω) ^ c₁ * (p : Ω) ^ c' * e0 - (p : Ω) ^ c' * e1 + (p : Ω) ^ c' * e2 + e4 - e3s
  refine ⟨σ⁻¹ ((p : Ω) ^ c₁ * (p : Ω) ^ c' * u0 - (p : Ω) ^ c' * w1 + (p : Ω) ^ c' * w2 + w4 - σ w3), isInt_gal _ ?_, ?_⟩
  · exact IsIntegral.sub (IsIntegral.add (IsIntegral.add (IsIntegral.sub
      (IsIntegral.mul (IsIntegral.mul (isInt_pow_p c₁) (isInt_pow_p c')) hu0)
      (IsIntegral.mul (isInt_pow_p c') hw1)) (IsIntegral.mul (isInt_pow_p c') hw2)) hw4) (isInt_gal σ hw3)
  · have KS := congrArg (⇑(σ⁻¹ : Gal p Ω)) K
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add, hs2, hsi, hfs] at KS
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add, hsi, pow_add]
    linear_combination KS

end GlobalTheory.EdgeAlg
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edge_class_cup_product_geometric : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ c₁ : ℕ, ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ (x y lz lq η : Gal p Ω → ZMod (p ^ n)) (f : Ω),
  (∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h) →
  IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq → IsInt p f → (∀ g ∈ Gn T L, g f = f) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c₁ * (((x g).val : Ω) * ((y h).val : Ω)) + (p : Ω) ^ c₁ * f * (((lz g).val : Ω) * ((lq h).val : Ω))) →
  ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L,
    Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun h => (p : Ω) ^ c * ((η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h).val : Ω) - (σ⁻¹ o - o - (p : Ω) ^ c * f * ((lz σ).val : Ω)) * ((lq h).val : Ω)) := by
  atlas_forward_decl GlobalTheory.EdgeAlg.edge_class_cup
end

section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EdgeLoc

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem pow_chain (f : ℕ → Ω) (hf : ∀ k, f (k + 1) ^ p = f k) (m k : ℕ) : f (m + k) ^ (p ^ k) = f m := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, hf, ih]

theorem zeta_le (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) : T.ζ L ^ (p ^ (L - n)) = T.ζ n := by
  have := pow_chain T.ζ T.ζpow n (L - n)
  rwa [Nat.add_sub_cancel' h] at this

theorem gn_fix_zeta (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {g : Gal p Ω} (hg : g ∈ Gn T L) :
    g (T.ζ n) = T.ζ n := by
  rw [← zeta_le T h, map_pow, ((Basic.mem_gn T L g).1 hg).1]

theorem kum_add (T : Tower p Ω) {n L : ℕ} (h : n ≤ L) {r : Ω} (hr : r ≠ 0) {x : Gal p Ω → ZMod (p ^ n)}
    (hx : IsKum T n (Gn T L) r x) {g g' : Gal p Ω} (hg : g ∈ Gn T L) (hg' : g' ∈ Gn T L) :
    x (g * g') = x g + x g' := by
  obtain ⟨χ, hχ⟩ := Basic.exists_isCyc T n
  rw [Basic.isKum_mul hχ hr hx hg hg', (Basic.isCyc_eq_one_iff hχ g).2 (gn_fix_zeta T h hg), one_mul]

variable (p) in
theorem adjoin_top (L : ℕ) : Algebra.adjoin (O0 p) {xn p L, yn p L} = ⊤ := by
  obtain ⟨b, hb⟩ := GlobalTheory.K5.OnFree.on_free p L
  rw [eq_top_iff]
  intro s _
  have hs : s ∈ Submodule.span (O0 p) (Set.range b) := b.span_eq ▸ Submodule.mem_top
  refine (Submodule.span_le (p := (Algebra.adjoin (O0 p) {xn p L, yn p L}).toSubmodule)).2 ?_ hs
  rintro _ ⟨⟨i, j⟩, rfl⟩
  rw [hb]
  show _ ∈ Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := Algebra.subset_adjoin (by simp)
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hx _) (Subalgebra.pow_mem _ hy _)

theorem emb_int (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (z : On p L) : IsInt p (ι z) := by
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p L
  haveI : Module.Finite (O0 p) (On p L) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p L) := Algebra.IsIntegral.of_finite _ _
  exact IsIntegral.map ι (Algebra.IsIntegral.isIntegral z)

theorem emb_fix (T : Tower p Ω) {L : ℕ} {ι : On p L →ₐ[O0 p] Ω} (hι : IsEmb T L ι) {g : Gal p Ω}
    (hg : g ∈ Gn T L) (z : On p L) : g (ι z) = ι z := by
  have h := AlgHom.ext_of_adjoin_eq_top (adjoin_top p L) (φ₁ := (g : Ω →ₐ[O0 p] Ω).comp ι) (φ₂ := ι) (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simp [hι.1, ((Basic.mem_gn T L g).1 hg).1]
    · simp [hι.2, ((Basic.mem_gn T L g).1 hg).2])
  exact congrArg (fun φ : On p L →ₐ[O0 p] Ω => φ z) h

theorem pint (k : ℕ) : IsInt p ((p : Ω) ^ k) := by
  have := Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  push_cast at this
  exact this

theorem qq_int (T : Tower p Ω) (L : ℕ) : IsInt p (T.qq L) := by
  refine ⟨Polynomial.X ^ (p ^ L) - Polynomial.C (qO p),
    Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]

theorem reb_mem {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    ψ y ∈ Algebra.adjoin (O0 p) {T.qq L} := by
  have h := ψ.mem_range_self y
  rw [hψ.rng] at h
  exact h

theorem reb_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) (y : O0 p) :
    IsInt p (ψ y) := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ integralClosure (O0 p) Ω :=
    Algebra.adjoin_le (by rw [Set.singleton_subset_iff, SetLike.mem_coe, mem_integralClosure_iff]; exact qq_int T L)
  exact h (reb_mem hψ y)

theorem reb_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {g : Gal p Ω}
    (hg : g (T.qq L) = T.qq L) (y : O0 p) : g (ψ y) = ψ y := by
  have h : Algebra.adjoin (O0 p) {T.qq L} ≤ AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id (O0 p) Ω) :=
    Algebra.adjoin_le (by
      rw [Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg)
  have h2 := h (reb_mem hψ y)
  rw [AlgHom.mem_equalizer] at h2
  simpa using h2

theorem ev_int {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') : IsInt p x ∧ IsInt p x' := by
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  exact ⟨(integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _),
    (integralClosure (O0 p) Ω).sum_mem fun t _ => (he t).1.mul (reb_int hψ _)⟩

theorem ev_fix {T : Tower p Ω} {L : ℕ} {ψ : O0 p →+* Ω} (hψ : IsReb T L ψ) {c : ℤ → Ω} {x x' : Ω}
    (h : Ev ψ c x x') {g : Gal p Ω} (hg : g ∈ Ggeo p Ω ⊓ Gn T L) : g x = x ∧ g x' = x' := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have hq : g (T.qq L) = T.qq L := ((Basic.mem_gn T L g).1 hg2).2
  obtain ⟨d, e, a, he, -, rfl, rfl⟩ := h
  constructor <;>
  · rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, hg1 _ (he t).2, reb_fix hψ hq]

theorem conj_mem {T : Tower p Ω} {L : ℕ} {σ g : Gal p Ω} (hσ : σ ∈ Gn T L) (hg : g ∈ Ggeo p Ω ⊓ Gn T L) :
    σ * g * σ⁻¹ ∈ Ggeo p Ω ⊓ Gn T L := by
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨fun z hz => ?_, (Gn T L).mul_mem ((Gn T L).mul_mem hσ hg2) ((Gn T L).inv_mem hσ)⟩
  have h1 : IsAlgZp p (σ⁻¹ z) := by
    obtain ⟨P, hP, e⟩ := hz
    refine ⟨P, hP, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ⁻¹ : Gal p Ω) : Ω →ₐ[O0 p] Ω) z (P.map (algebraMap ℤ_[p] (O0 p)))
    rw [e, map_zero] at this
    simpa using this
  show σ (g (σ⁻¹ z)) = z
  rw [hg1 _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem algZp_root {κ ρ : Ω} (hκ : IsAlgZp p κ) {m : ℕ} (hm : 0 < m) (h : ρ ^ m = κ) : IsAlgZp p ρ := by
  obtain ⟨P, hP, e⟩ := hκ
  refine ⟨Polynomial.expand ℤ_[p] m P, (Polynomial.expand_ne_zero hm).2 hP, ?_⟩
  rw [Polynomial.map_expand, Polynomial.expand_aeval, h, e]

theorem kum_rel (T : Tower p Ω) {n : ℕ} {H : Subgroup (Gal p Ω)} {θ ρ ra rb : Ω}
    {e ka kb : Gal p Ω → ZMod (p ^ n)}
    (hθ : IsKum T n H θ e) (ha : IsKum T n H ra ka) (hb : IsKum T n H rb kb)
    (hρ : ∀ g ∈ H, g ρ = ρ) (hrel : θ * rb = ρ * ra) (hne : θ * rb ≠ 0) {g : Gal p Ω} (hg : g ∈ H) :
    Cong p n (((e g).val : Ω) + ((kb g).val : Ω)) ((ka g).val : Ω) := by
  have h1 := congrArg g hrel
  rw [map_mul, map_mul, hθ g hg, hb g hg, hρ g hg, ha g hg] at h1
  have h2 : T.ζ n ^ ((e g).val + (kb g).val) * (θ * rb) = T.ζ n ^ (ka g).val * (θ * rb) := by
    rw [pow_add]; linear_combination h1 - T.ζ n ^ (ka g).val * hrel
  have h3 := mul_right_cancel₀ hne h2
  rw [Basic.zeta_pow_eq_iff] at h3
  have := Basic.cong_natCast (Ω := Ω) h3
  push_cast at this
  exact this

end GlobalTheory.EdgeLoc

namespace GlobalTheory.EdgeLoc

theorem edge_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ (ψ : O0 p →+* Ω), IsReb T L ψ → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ x y lz η : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r x → IsKum T n (Gn T L) s y → IsKum T n (Gn T L) (T.ζ (L + n)) lz →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), x g * y h = η h - η (g * h) + η g) →
  (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∃ S : Finset Ω, ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), (∀ z ∈ S, h z = g z) → η h = η g) →
  ∃ o : Ω, IsInt p o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ ∀ σ ∈ Gn T L, ∀ (θ κ a a' b b' : Ω) (ca cb : ℤ → Ω),
    IsKum T n (Ggeo p Ω ⊓ Gn T L) θ (fun h => η (σ * h * σ⁻¹) - η h - x h * y σ + x σ * y h) →
    κ ≠ 0 → IsAlgZp p κ → θ ^ (p ^ n) * b = κ * a → Ev ψ ca a a' → Ev ψ cb b b' → a ≠ 0 → IsInt p a⁻¹ → b ≠ 0 → IsInt p b⁻¹ →
    Cong p n ((p : Ω) ^ c * (a' / a - b' / b)) (σ⁻¹ o - o - (p : Ω) ^ c * ι (α * β' - β * α') * ((lz σ).val : Ω)) := by
  intro p _ hp2
  obtain ⟨c₁, h53⟩ := GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL p hp2
  obtain ⟨c₂, hed⟩ := GlobalTheory.T.edge_class_cup_product_geometric p hp2 c₁
  obtain ⟨c₃, hgeo⟩ := GlobalTheory.T.kummerCocycle_value_expansion_eq_logDeriv_smul p hp2
  obtain ⟨c₄, h71⟩ := GlobalTheory.T.geometric_level_h1_coboundary p hp2
  refine ⟨c₂ + c₃ + c₄, ?_⟩
  intro Ω _ _ hΩ T L n hnL hn1 ψ hψ ι hι u v α β α' β' hu hv r s hr hs x y lz η hx hy hlz hcup hloc
  haveI := hΩ.clo
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hr; exact (u.isUnit.map ι).ne_zero hr.symm
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [zero_pow hpn] at hs; exact (v.isUnit.map ι).ne_zero hs.symm
  obtain ⟨lq, hlq⟩ := Basic.exists_isKum T n (Gn T L) (Basic.qq_ne_zero T (L + n)) (fun g hg => by
    rw [pow_chain T.qq T.qpow L n, ((Basic.mem_gn T L g).1 hg).2])
  have hcob := h53 Ω hΩ T L n hnL hn1 ι hι u v α β α' β' hu hv r s hr hs x y lz lq hx hy hlz hlq
  have hadd : ∀ g ∈ Gn T L, ∀ h ∈ Gn T L, x (g * h) = x g + x h ∧ y (g * h) = y g + y h :=
    fun g hg h hh => ⟨kum_add T hnL hr0 hx hg hh, kum_add T hnL hs0 hy hg hh⟩
  obtain ⟨o₁, ho₁i, ho₁f, hE⟩ := hed Ω hΩ T L n hnL x y lz lq η (ι (α * β' - β * α')) hadd hlz hlq
    (emb_int L ι _) (fun g hg => emb_fix T hι hg _) hcup hloc hcob
  have hlqΔ : IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq := fun g hg => hlq g (Subgroup.mem_inf.1 hg).2
  obtain ⟨-, h71k⟩ := h71 Ω hΩ T L n hnL lq hlqΔ
  refine ⟨(p : Ω) ^ (c₃ + c₄) * o₁, (pint _).mul ho₁i, fun g hg => by rw [map_mul, map_pow, map_natCast, ho₁f g hg], ?_⟩
  intro σ hσ θ κ a a' b b' ca cb hθ hκ0 hκ hrel hea heb ha0 hai hb0 hbi
  have hpn0 : 0 < p ^ n := Nat.pos_of_ne_zero hpn
  obtain ⟨ra, hra⟩ := IsAlgClosed.exists_pow_nat_eq a hpn0
  obtain ⟨rb, hrb⟩ := IsAlgClosed.exists_pow_nat_eq b hpn0
  have hra0 : ra ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hra; exact ha0 hra.symm
  have hrb0 : rb ≠ 0 := by rintro rfl; rw [zero_pow hpn] at hrb; exact hb0 hrb.symm
  obtain ⟨ka, hka⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hra0 (fun g hg => by
    rw [hra, (ev_fix hψ hea hg).1])
  obtain ⟨kb, hkb⟩ := Basic.exists_isKum T n (Ggeo p Ω ⊓ Gn T L) hrb0 (fun g hg => by
    rw [hrb, (ev_fix hψ heb hg).1])
  obtain ⟨xa, hxai, hxa⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ ca a a' ra hea ha0 hai hra ka lq hka hlqΔ
  obtain ⟨xb, hxbi, hxb⟩ := hgeo Ω hΩ T L n hnL hn1 ψ hψ cb b b' rb heb hb0 hbi hrb kb lq hkb hlqΔ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have hθ0 : θ ≠ 0 := by
    rintro rfl; rw [zero_pow hpn, zero_mul] at hrel; exact mul_ne_zero hκ0 ha0 hrel.symm
  set ρ : Ω := θ * rb / ra with hρdef
  have hρpow : ρ ^ (p ^ n) = κ := by
    rw [hρdef, div_pow, mul_pow, hra, hrb, hrel, mul_div_assoc, div_self ha0, mul_one]
  have hρalg : IsAlgZp p ρ := algZp_root hκ hpn0 hρpow
  have hρfix : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g ρ = ρ := fun g hg => (Subgroup.mem_inf.1 hg).1 ρ hρalg
  have hrel' : θ * rb = ρ * ra := by rw [hρdef]; field_simp
  have hK := fun g (hg : g ∈ Ggeo p Ω ⊓ Gn T L) =>
    kum_rel T hθ hka hkb hρfix hrel' (mul_ne_zero hθ0 hrb0) hg
  obtain ⟨we, hwei, hwe⟩ := hE σ hσ
  have key : ∀ w, σ⁻¹ (σ w) = w := fun w => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hσo : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g (σ⁻¹ o₁) = σ⁻¹ o₁ := fun g hg => by
    have h1 := ho₁f _ (conj_mem hσ hg)
    calc g (σ⁻¹ o₁) = σ⁻¹ (σ (g (σ⁻¹ o₁))) := (key _).symm
      _ = σ⁻¹ ((σ * g * σ⁻¹) o₁) := rfl
      _ = σ⁻¹ o₁ := by rw [h1]
  obtain ⟨X, hXd⟩ : ∃ X : Ω, X = (p : Ω) ^ c₃ * (σ⁻¹ o₁ - o₁ - (p : Ω) ^ c₂ * ι (α * β' - β * α') * ((lz σ).val : Ω))
      - (p : Ω) ^ (c₂ + c₃) * (a' / a - b' / b) := ⟨_, rfl⟩
  have hXi : IsInt p X := by
    have ha' := (ev_int hψ hea).2
    have hb' := (ev_int hψ heb).2
    have hfi : IsInt p (ι (α * β' - β * α')) := emb_int L ι _
    have hσi : IsInt p (σ⁻¹ o₁) := Basic.isInt_gal _ ho₁i
    have hlzi : IsInt p (((lz σ).val : Ω)) := by
      have := Basic.isInt_intCast (p := p) (Ω := Ω) ((lz σ).val : ℤ)
      exact_mod_cast this
    rw [hXd, div_eq_mul_inv, div_eq_mul_inv]
    exact ((pint _).mul (((hσi.sub ho₁i).sub (((pint _).mul hfi).mul hlzi)))).sub
      ((pint _).mul ((ha'.mul hai).sub (hb'.mul hbi)))
  have hXf : ∀ g ∈ Ggeo p Ω ⊓ Gn T L, g X = X := fun g hg => by
    have hg2 := (Subgroup.mem_inf.1 hg).2
    rw [hXd]
    simp only [map_sub, map_mul, map_div₀, map_pow, map_natCast, hσo g hg, ho₁f g hg,
      emb_fix T hι hg2, (ev_fix hψ hea hg).1, (ev_fix hψ hea hg).2, (ev_fix hψ heb hg).1, (ev_fix hψ heb hg).2]
  have hXcob : Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => X * ((lq g).val : Ω)) := by
    refine ⟨(p : Ω) ^ c₂ * (xa - xb) - (p : Ω) ^ c₃ * we,
      ((pint _).mul (hxai.sub hxbi)).sub ((pint _).mul hwei), fun g hg => ?_⟩
    obtain ⟨z1, hz1, e1⟩ := hwe g hg
    obtain ⟨z2, hz2, e2⟩ := hxa g hg
    obtain ⟨z3, hz3, e3⟩ := hxb g hg
    obtain ⟨z4, hz4, e4⟩ := hK g hg
    refine ⟨(p : Ω) ^ (c₂ + c₃) * z4 + (p : Ω) ^ c₂ * (z2 - z3) - (p : Ω) ^ c₃ * z1,
      (((pint _).mul hz4).add ((pint _).mul (hz2.sub hz3))).sub ((pint _).mul hz1), ?_⟩
    rw [hXd]
    simp only [map_sub, map_mul, map_pow, map_natCast] at e1 e2 e3 e4 ⊢
    linear_combination -(p : Ω) ^ c₃ * e1 + (p : Ω) ^ c₂ * e2 - (p : Ω) ^ c₂ * e3 + (p : Ω) ^ (c₂ + c₃) * e4
  obtain ⟨z, hz, ez⟩ := h71k X hXi hXf hXcob
  refine ⟨-z, hz.neg, ?_⟩
  rw [map_mul, map_pow, map_natCast]
  rw [hXd] at ez
  linear_combination -ez
end GlobalTheory.EdgeLoc
end
end
