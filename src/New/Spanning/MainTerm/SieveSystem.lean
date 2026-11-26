module

import TauCeti.MeasureTheory.Integral.SieveSystem
public import Lib.General.Groups.BesselGroups
public import Lib.General.Measure.IntegralOperators

/-!
# Sieve systems over places: products, positivity and lower semicontinuity

An abstract sieve. A system `New.SieveSystem` over a ring `C` with a measure (a place, or a product
of places) consists of forms `J i p q`, `i ≤ n + 1`, on pairs of sequences ("heads"), each but the
last the integral of the next one over a common entry, with bounds `B₀`, `Λ`, `β`.

* `New.SieveSystem.pi`: a product of finitely many systems on `ℂ` (one for each real
  place in the application) and one more system is a system.
* `New.SieveSystem.integrable_sum_update`, `New.SieveSystem.integral_sum_update`,
  `New.SieveSystem.norm_integral_mul_sum_update_le`: sum the forms `J (i + 1)` over all pairs of
  heads from one finite family, with a common entry at position `i ≤ n`. The sum is integrable in
  the common entry, its integral is the sum of the `J i`, and its twisted integrals are bounded by
  `β` and `Λ`.
* `New.SieveSystem.sum_nonneg`, `New.SieveSystem.lowerSemicontinuousAt_sum`: such a sum is
  nonnegative, and its real part is lower semicontinuous in a parameter `x : C` at each point where
  every head is continuous.
* `New.dampedPower`, `New.headWeight`: the decay in the frequency and the weights `Λ` of the heads
  at the real places.

The product, sum-integral, positivity and lower-semicontinuity results are deduced from
`TauCeti.MeasureTheory.Integral.SieveSystem`.

## Relation to the literature

See `New.Spanning.MainTerm.GlobalSieve` for related work.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Function Matrix ComplexOrder

namespace New

/-- The gain at the ratio `r`: the function `r ^ k * min 1 r ^ 6`. -/
def dampedPower (k : ℕ) (r : ℝ) : ℝ := r ^ k * min 1 r ^ 6

/-- The weight of a head `p` (with entries in `ℂˣ`) of length `i` at a real place. It is zero unless
the partial products `δ = p 0 * ⋯ * p l`, `l < i`, have modulus at most `R`, and then it is the
product of the numbers `max 1 ‖δ‖⁻¹ ^ K`. -/
def headWeight (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : ℝ :=
  ∏ l ∈ range i,
    let δ : ℂ := ∏ a ∈ range (l + 1), (p a : ℂ)
    if ‖δ‖ ≤ R then max 1 ‖δ‖⁻¹ ^ K else 0

lemma headWeight_nonneg (R : ℝ) (K i : ℕ) (p : ℕ → ℂˣ) : 0 ≤ headWeight R K i p :=
  prod_nonneg fun _ _ ↦ ite_nonneg (by positivity) le_rfl

variable {C U τ : Type} [CommRing C] [MeasureSpace C] [TopologicalSpace U] [Fintype τ]

/-- The axioms of the sieve at a place or a product of places: `C` is a ring with a measure, `u c`
is the entry given by `c ∈ C`, and `ι` maps entries back to `C` (in the applications `x ↦ x⁻¹`,
times a constant at the finite places). The forms `J i p q`, `i ≤ n + 1`, pair two sequences of
entries, called heads, with weights `Λ i p`. The field `integrable_and_integral_update` makes each
form but the top one the integral of the next over a common entry, and bounds the same integral
twisted by `ψ (ξ * c)` at a unit `ξ` in terms of the decay `β ξ`. The top form `J (n + 1)` is
continuous, and positive semidefinite on heads with a common entry at position `n`. The bottom form
`J 0` has modulus at most `En`. -/
structure SieveSystem (u : C → U) (ι : U → C) (n : ℕ) (J : ℕ → (ℕ → U) → (ℕ → U) → ℂ) (ψ : C → ℂ)
    (En : ℝ) (Λ : ℕ → (ℕ → U) → ℝ) (β : C → ℝ) : Prop where
  /-- The function `ψ` takes the value `1` at `0`. -/
  psi_zero : ψ 0 = 1
  /-- For `i ≤ n`, give both heads the entry `u c` at position `i`. Then `ψ (ξ * c)` times the form
  `J (i + 1)` is integrable in `c`; its integral is `J i p q` if `ξ = 0`, and has modulus at most
  `β ξ * (Λ i p * Λ i q)` if `ξ` is a unit. -/
  integrable_and_integral_update (i : ℕ) (p q : ℕ → U) (ξ : C) :
      i ≤ n →
      let f (c : C) : ℂ := ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))
      Integrable f ∧
      (ξ = 0 → ∫ c : C, f c = J i p q) ∧
      (IsUnit ξ → ‖∫ c : C, f c‖ ≤ β ξ * (Λ i p * Λ i q))
  /-- The top form `J (n + 1)` is a positive semidefinite kernel on heads with the same entry at
  position `n`. -/
  posSemidef {κ : Type} [Fintype κ] (a : κ → ℕ → U) (t : U) :
      (∀ i : κ, a i n = t) → (Matrix.of fun i j : κ ↦ J (n + 1) (a i) (a j)).PosSemidef
  /-- The top form `J (n + 1)` is jointly continuous. -/
  continuous : Continuous (J (n + 1)).uncurry
  /-- The bottom form `J 0` has modulus at most `En`. -/
  norm_bot_le (p q : ℕ → U) : ‖J 0 p q‖ ≤ En
  /-- For `i < n`, if `ξ = ι (p i) - ι (q i)` is a unit, then `J (i + 1) p q` has modulus at most
  `β ξ * (Λ (i + 1) p * Λ (i + 1) q)`. -/
  norm_le_of_isUnit_sub (i : ℕ) (p q : ℕ → U) :
      i < n →
      let ξ : C := ι (p i) - ι (q i)
      IsUnit ξ → ‖J (i + 1) p q‖ ≤ β ξ * (Λ (i + 1) p * Λ (i + 1) q)

variable {u : C → U} {ι : U → C} {n : ℕ} {J : ℕ → (ℕ → U) → (ℕ → U) → ℂ} {ψ : C → ℂ} {B₀ : ℝ}
  {Λ : ℕ → (ℕ → U) → ℝ} {β : C → ℝ}

/-- The component at the complex factor `v` of a head `p` with entries in `(τ → ℂˣ) × U`: the
sequence `k ↦ (p k).1 v`. -/
def headAt (v : τ) (p : ℕ → (τ → ℂˣ) × U) : ℕ → ℂˣ := (fun y : (τ → ℂˣ) × U ↦ y.1 v) ∘ p

/-- For `i ≤ n`, give both heads the entry `u c` at position `i`. Then `ψ (ξ * c)` times the form
`J (i + 1)` is integrable in `c`. -/
lemma SieveSystem.integrable_mul_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) (ξ : C) :
    Integrable fun c : C ↦ ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c)) :=
  (K.integrable_and_integral_update i p q ξ hi).1

/-- For `i ≤ n`, the form `J (i + 1)` is integrable in a common entry `u c` at position `i`. -/
lemma SieveSystem.integrable_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) : Integrable fun c : C ↦ J (i + 1) (update p i (u c)) (update q i (u c)) := by
  simpa only [zero_mul, K.psi_zero, one_mul] using K.integrable_mul_update hi p q 0

/-- For `i ≤ n`, the form `J i` is the integral of `J (i + 1)` over a common entry `u c` at
position `i`. -/
lemma SieveSystem.integral_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (p q : ℕ → U) : ∫ c : C, J (i + 1) (update p i (u c)) (update q i (u c)) = J i p q := by
  obtain ⟨-, h_zero, -⟩ := K.integrable_and_integral_update i p q 0 hi
  simpa only [zero_mul, K.psi_zero, one_mul] using h_zero rfl

/-- For `i ≤ n` and a unit `ξ`, the integral of `J (i + 1)` over a common entry `u c` at position
`i`, twisted by `ψ (ξ * c)`, has modulus at most `β ξ * (Λ i p * Λ i q)`. -/
lemma SieveSystem.norm_integral_mul_update_le (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (p q : ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) * J (i + 1) (update p i (u c)) (update q i (u c))‖ ≤
      β ξ * (Λ i p * Λ i q) :=
  (K.integrable_and_integral_update i p q ξ hi).2.2 hξ

private lemma SieveSystem.toTauCeti (K : SieveSystem u ι n J ψ B₀ Λ β) :
    TauCeti.SieveSystem u ι n J ψ B₀ Λ β where
  psi_zero := K.psi_zero
  integrable_mul_update _ hi := K.integrable_mul_update hi
  integral_update _ hi := K.integral_update hi
  norm_integral_mul_update_le _ hi p q {_} hξ := K.norm_integral_mul_update_le hi p q hξ
  posSemidef := K.posSemidef
  continuous := K.continuous
  norm_bot_le := K.norm_bot_le
  norm_le_of_isUnit_sub i hi p q hξ := K.norm_le_of_isUnit_sub i p q hi hξ

private lemma SieveSystem.ofTauCeti (K : TauCeti.SieveSystem u ι n J ψ B₀ Λ β) :
    SieveSystem u ι n J ψ B₀ Λ β where
  psi_zero := K.psi_zero
  integrable_and_integral_update i p q ξ hi :=
    ⟨K.integrable_mul_update i hi p q ξ,
      fun h0 ↦ by simpa [h0, K.psi_zero] using K.integral_update i hi p q,
      fun hξ ↦ K.norm_integral_mul_update_le i hi p q hξ⟩
  posSemidef := K.posSemidef
  continuous := K.continuous
  norm_bot_le := K.norm_bot_le
  norm_le_of_isUnit_sub i p q hi hξ := K.norm_le_of_isUnit_sub i hi p q hξ

/-- A finite product of sieve systems is a sieve system.

Let `K` be such a system on `C` (with s-finite volume), and for each `v` in the finite type `τ` take
a system on `ℂ` with forms `J' v`, bounds `B₀' v`, `Λ'`, `γ v`, entry map `unitOrOne`, map `ι'` back
to `ℂ` and twist `wave`. Then the products of the forms, twists and bounds make a system on
`(τ → ℂ) × C`, each form and weight being evaluated on the components of the heads in its factor:
`headAt v p = fun k ↦ (p k).1 v` at `v`, and `Prod.snd ∘ p` in `U`. -/
lemma SieveSystem.pi (K : SieveSystem u ι n J ψ B₀ Λ β) [SFinite (volume : Measure C)] {ι' : ℂˣ → ℂ}
    {Λ' : ℕ → (ℕ → ℂˣ) → ℝ} {J' : τ → ℕ → (ℕ → ℂˣ) → (ℕ → ℂˣ) → ℂ} {B₀' : τ → ℝ} {γ : τ → ℂ → ℝ}
    (h_factor : ∀ v : τ, SieveSystem unitOrOne ι' n (J' v) wave (B₀' v) Λ' (γ v)) :
    SieveSystem (Prod.map (fun x : τ → ℂ ↦ unitOrOne ∘ x) u)
      (Prod.map (fun y : τ → ℂˣ ↦ ι' ∘ y) ι) n
      (fun (i : ℕ) (p q : ℕ → (τ → ℂˣ) × U) ↦
        (∏ v : τ, J' v i (headAt v p) (headAt v q)) * J i (Prod.snd ∘ p) (Prod.snd ∘ q))
      (fun x : (τ → ℂ) × C ↦ (∏ v : τ, wave (x.1 v)) * ψ x.2)
      ((∏ v : τ, B₀' v) * B₀)
      (fun (i : ℕ) (p : ℕ → (τ → ℂˣ) × U) ↦ (∏ v : τ, Λ' i (headAt v p)) * Λ i (Prod.snd ∘ p))
      fun x : (τ → ℂ) × C ↦ (∏ v : τ, γ v (x.1 v)) * β x.2 :=
  SieveSystem.ofTauCeti ((TauCeti.SieveSystem.pi fun v ↦ (h_factor v).toTauCeti).prod K.toTauCeti)

/-- For `i ≤ n` and finitely many heads `a p`, the sum of `J (i + 1)` over all pairs of heads is
integrable in a common entry `u c` at position `i`. -/
lemma SieveSystem.integrable_sum_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) :
    Integrable fun c : C ↦
      ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c)) :=
  K.toTauCeti.integrable_sum_update hi a

/-- The recursion summed over all pairs from finitely many heads `a p`: for `i ≤ n`, the sum of the
forms `J i` is the integral of the sum of the forms `J (i + 1)` over a common entry `u c` at
position `i`. -/
lemma SieveSystem.integral_sum_update (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) :
    ∫ c : C, ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c)) =
      ∑ p : τ, ∑ q : τ, J i (a p) (a q) :=
  K.toTauCeti.integral_sum_update hi a

/-- For `i ≤ n`, finitely many heads `a p` and a unit `ξ`, sum the forms `J (i + 1)` of the system
`K` over all pairs of heads with a common entry `u c` at position `i`. The integral of this sum
twisted by `ψ (ξ * c)` has modulus at most `β ξ * (∑ p, Λ i (a p)) ^ 2`, with `Λ` the head weights
and `β` the decay of `K`. -/
lemma SieveSystem.norm_integral_mul_sum_update_le (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (a : τ → ℕ → U) {ξ : C} (hξ : IsUnit ξ) :
    ‖∫ c : C, ψ (ξ * c) *
        ∑ p : τ, ∑ q : τ, J (i + 1) (update (a p) i (u c)) (update (a q) i (u c))‖ ≤
      β ξ * (∑ p : τ, Λ i (a p)) ^ 2 :=
  K.toTauCeti.norm_integral_mul_sum_update_le hi a hξ

/-- In a sieve system `K` with forms `J`, if finitely many heads `a p` have a common entry `t` at
position `i ≤ n`, then the sum of `J (i + 1)` over all pairs of heads is a nonnegative real
number. -/
lemma SieveSystem.sum_nonneg (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ} (hi : i ≤ n)
    (a : τ → ℕ → U) {t : U} (h_common : ∀ p : τ, a p i = t) :
    0 ≤ ∑ p : τ, ∑ q : τ, J (i + 1) (a p) (a q) :=
  K.toTauCeti.sum_nonneg hi a h_common

variable [TopologicalSpace C] [FirstCountableTopology C]

/-- In a sieve system `K` with forms `J`, let finitely many heads `b y p`, depending on `y : C`,
have a common entry `c y` at position `i ≤ n` for each `y`. The sum of `J (i + 1)` over all pairs
of heads, which is a nonnegative real number, is lower semicontinuous in `y` at each point `x` where
the heads are continuous. This is stated for `ENNReal.ofReal` of its real part. -/
lemma SieveSystem.lowerSemicontinuousAt_sum (K : SieveSystem u ι n J ψ B₀ Λ β) {i : ℕ}
    (hi : i ≤ n) (b : C → τ → ℕ → U) {c : C → U} (h_common : ∀ (y : C) (p : τ), b y p i = c y)
    {x : C} (h_cont : ∀ p : τ, ContinuousAt (fun y : C ↦ b y p) x) :
    LowerSemicontinuousAt
      (fun y : C ↦ ENNReal.ofReal (RCLike.re (∑ p : τ, ∑ q : τ, J (i + 1) (b y p) (b y q)))) x :=
  K.toTauCeti.lowerSemicontinuousAt_sum hi b h_common h_cont

end New

end
