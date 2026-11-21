import ReciprocityTheory.DualLattices.TangentPairingStatement

section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp

namespace BX

variable (B : BX R₀)

def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)

lemma evK_ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker)
    (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) :
    B.evK π h (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) = ξ * B.ev h v := by
  induction v using TensorProduct.induction_on with
  | zero => simp [evK, ev]
  | tmul g r =>
    simp only [evK, ev, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mul'_apply,
      Submodule.subtype_apply]
    show h g * (ξ * r) = ξ * (h g * r)
    ring
  | add x y hx hy =>
    simp only [evK, ev, map_add] at hx hy ⊢
    rw [hx, hy, mul_add]

end BX

def ThmALevelStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) (Dp : DualPair R)
    (N : ℕ) (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ})
    (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (v w : B.gg ⊗[R₀] (R' : Type u)) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ) (c : (R' : Type u)) (e₀ : ℤ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) v) →
      N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) (TensorProduct.map LinearMap.id (ξmul π ξ hξ) w) →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + e₀ * c * ξ →
      π.1 (e₀ * c) = π.1 (B.ev ht v) - π.1 (B.ev hs w)


end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATower (R₀ : Type u) [CommRing R₀] (p : ℕ) where
  O : LAlg R₀
  R' : ℕ → LAlg R₀
  R : ℕ → LAlg R₀
  π : ∀ n, LHom (R' n) (R n)
  q : ∀ n, LHom O (R n)
  ξ : ∀ n, (R' n : Type u)
  surj : ∀ n, Function.Surjective (π n).1
  ker_eq : ∀ n, RingHom.ker (π n).1 = Ideal.span {ξ n}
  ξ_sq : ∀ n, ξ n * ξ n = 0
  ann : ∀ n (a : (R' n : Type u)), a * ξ n = 0 → a ∈ Ideal.span {ξ n}
  char : ∀ n, ((p ^ (n + 1) : ℕ) : (R' n : Type u)) = 0
  sep : ∀ a : (O : Type u), (∀ n, (q n).1 a = 0) → a = 0
  c : (O : Type u)
  cp : ∀ n, (R' n : Type u)
  cp_spec : ∀ n, (π n).1 (cp n) = (q n).1 c
  zh : ∀ n, (R' n : Type u)ˣ
  zh_pow : ∀ n, (zh n : (R' n : Type u)) ^ (p ^ (n + 1)) = 1 + cp n * ξ n
  ζ : ∀ n, (O : Type u)ˣ
  ζ_spec : ∀ n, (q n).1 (ζ n : (O : Type u)) = (π n).1 (zh n : (R' n : Type u))

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.ξ_mem {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : Tw.ξ n ∈ (Tw.π n).ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Tw.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma ATower.sqZero {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : (Tw.π n).SqZero := ⟨Tw.surj n, by
    rw [Tw.ker_eq, sq, Ideal.span_singleton_mul_span_singleton, Tw.ξ_sq, Ideal.span_singleton_eq_bot]⟩

def NsetExpInjectiveSurjective (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ (Dp : ∀ n, DualPair (Tw.R n)) (ι : Type) (τ : ι → ℕ → B.G Tw.O)
    (E : ι → ι → (Tw.O : Type u)) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    ∀ i j, Tw.c * E i j = B.ev (ht j) (bt i) - B.ev (ht i) (bt j)

end ReciprocityTheory.PGsh
end
end
