import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def pInt (p : ℕ) : Submodule R C := Submodule.span R {(p : C)}

def pFun (p : ℕ) (N : Type) : Submodule R (N → C) :=
  Submodule.pi Set.univ fun _ => pInt R p

def addFun (p : ℕ) (N : Type) [AddCommGroup N] : Submodule R (N → C) where
  carrier := {f | ∀ x y, f (x + y) - f x - f y ∈ pInt (C := C) R p}
  add_mem' := by
    intro f g hf hg x y
    have h := Submodule.add_mem _ (hf x y) (hg x y)
    convert h using 1
    simp only [Pi.add_apply]; ring
  zero_mem' := by intro x y; simp
  smul_mem' := by
    intro c f hf x y
    have h := Submodule.smul_mem _ c (hf x y)
    convert h using 1
    simp only [Pi.smul_apply, smul_sub]

def linFun (p : ℕ) (N : Type) [AddCommGroup N] : Submodule R (N → C) :=
  intFun R N ⊓ addFun R p N

variable {R}

def afFun (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) : Submodule R (N → C) :=
  M ⊓ addFun R p N

abbrev AFQuot (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) :=
  linFun (C := C) R p N ⧸ (afFun p M ⊔ pFun R p N).comap (linFun (C := C) R p N).subtype

def invFun {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) (K : AddSubgroup N) :
    Submodule R (N → C) where
  carrier := {g | g ∈ M ∧ ∀ x, ∀ k ∈ K, g (x + k) = g x}
  add_mem' := by
    intro f g hf hg
    exact ⟨M.add_mem hf.1 hg.1, fun x k hk => by simp [hf.2 x k hk, hg.2 x k hk]⟩
  zero_mem' := ⟨M.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c f hf
    exact ⟨M.smul_mem c hf.1, fun x k hk => by simp [hf.2 x k hk]⟩

def GenAF (p : ℕ) {N : Type} [AddCommGroup N] (M : Submodule R (N → C)) (K : AddSubgroup N) : Prop :=
  invFun M K ≤ Subalgebra.toSubmodule (Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C)))

def afLat (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R ((ι → ZMod p) → C)) : Submodule R (ι → R) where
  carrier := {l | ∃ g ∈ M, ∀ x, g x - algebraMap R C (∑ i, l i * ((x i).val : R)) ∈ pInt (C := C) R p}
  add_mem' := by
    rintro l l' ⟨g, hg, h⟩ ⟨g', hg', h'⟩
    refine ⟨g + g', M.add_mem hg hg', fun x => ?_⟩
    convert Submodule.add_mem _ (h x) (h' x) using 1
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add]; ring
  zero_mem' := ⟨0, M.zero_mem, fun x => by simp⟩
  smul_mem' := by
    rintro c l ⟨g, hg, h⟩
    refine ⟨c • g, M.smul_mem c hg, fun x => ?_⟩
    convert Submodule.smul_mem _ c (h x) using 1
    simp only [Pi.smul_apply, smul_eq_mul, smul_sub, mul_assoc, ← Finset.mul_sum, map_mul,
      Algebra.smul_def]
    ring

def IsTight (v : Valuation C NNReal) (p : ℕ) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (M : Submodule R (N → C)) : Prop :=
  ∃ cA cN cO : NNReal, HasLen v R (AFQuot p M) cA ∧ HasColen R v M cN ∧ HasLen v R (OmAA M) cO ∧
    cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 ∧ cO ^ Fintype.card N = cN ^ 2

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

def IsFund (p : ℕ) (σ : MulChar F R) : Prop :=
  ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}

variable (F) in

def FStable (M : Submodule R (N → C)) : Prop :=
  ∀ a : F, ∀ g ∈ M, (fun x => g (a • x)) ∈ M

def eig (M : Submodule R (N → C)) (χ : MulChar F R) : Submodule R (N → C) where
  carrier := {g | g ∈ M ∧ ∀ (a : F) x, g (a • x) = algebraMap R C (χ a) * g x}
  add_mem' := by
    intro f g hf hg
    exact ⟨M.add_mem hf.1 hg.1, fun a x => by simp [hf.2 a x, hg.2 a x, mul_add]⟩
  zero_mem' := ⟨M.zero_mem, fun _ _ => by simp⟩
  smul_mem' := by
    intro c f hf
    refine ⟨M.smul_mem c hf.1, fun a x => ?_⟩
    simp only [Pi.smul_apply, hf.2 a x, Algebra.smul_def]; ring

abbrev OmType (M : Submodule R (N → C)) (χ : MulChar F R) :=
  eig M χ ⧸ (sqIdeal (augIdeal M)).comap (eig M χ).subtype

def proj [Fintype F] [DecidableEq F] (χ : MulChar F R) (g : N → C) : N → C :=
  fun x => (Fintype.card Fˣ : C)⁻¹ * ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x)

def xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) : Ideal R :=
  M.comap (LinearMap.toSpanSingleton R (F → C) fun a => algebraMap R C (χ a))

def stepOrder (M : Submodule R (N → C)) (K : Submodule F N) (t : N) : Submodule R (F → C) :=
  (invFun M K.toAddSubgroup).map (LinearMap.funLeft R C fun a : F => a • t)

def stepOrderRes (M : Submodule R (N → C)) (K : Submodule F N) (t : N) : Submodule R (F → C) where
  carrier := {h | ∃ g ∈ M, ∀ a : F, ∀ k ∈ K, g (a • t + k) = h a}
  add_mem' := by
    rintro h h' ⟨g, hg, e⟩ ⟨g', hg', e'⟩
    exact ⟨g + g', M.add_mem hg hg', fun a k hk => by simp [e a k hk, e' a k hk]⟩
  zero_mem' := ⟨0, M.zero_mem, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c h ⟨g, hg, e⟩
    exact ⟨c • g, M.smul_mem c hg, fun a k hk => by simp [e a k hk]⟩

def idealX (M : Submodule R (N → C)) (K : Submodule F N) (t : N) (χ : MulChar F R) : Ideal R :=
  xIdeal (stepOrder M K t) χ

def idealD (p : ℕ) (M : Submodule R (N → C)) (K : Submodule F N) (t : N) (χ : MulChar F R) :
    Ideal R where
  carrier := {c | ∃ g ∈ afFun p M,
    (∀ (a : F) x, g (a • x) - algebraMap R C (χ a) * g x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, g k ∈ pInt (C := C) R p) ∧ g t - algebraMap R C c ∈ pInt (C := C) R p}
  add_mem' := by
    rintro c c' ⟨g, hg, h1, h2, h3⟩ ⟨g', hg', h1', h2', h3'⟩
    refine ⟨g + g', Submodule.add_mem _ hg hg', fun a x => ?_, fun k hk => ?_, ?_⟩
    · convert Submodule.add_mem _ (h1 a x) (h1' a x) using 1
      simp only [Pi.add_apply]; ring
    · exact Submodule.add_mem _ (h2 k hk) (h2' k hk)
    · convert Submodule.add_mem _ h3 h3' using 1
      simp only [Pi.add_apply, map_add]; ring
  zero_mem' := ⟨0, Submodule.zero_mem _, fun _ _ => by simp, fun _ _ => by simp, by simp⟩
  smul_mem' := by
    rintro r c ⟨g, hg, h1, h2, h3⟩
    refine ⟨r • g, Submodule.smul_mem _ r hg, fun a x => ?_, fun k hk => ?_, ?_⟩
    · convert Submodule.smul_mem _ r (h1 a x) using 1
      simp only [Pi.smul_apply, Algebra.smul_def]; ring
    · exact Submodule.smul_mem _ r (h2 k hk)
    · convert Submodule.smul_mem _ r h3 using 1
      simp only [Pi.smul_apply, Algebra.smul_def, smul_eq_mul, map_mul, Algebra.algebraMap_self,
        RingHom.id_apply]; ring

def flagSub {n : ℕ} (b : Module.Basis (Fin n) F N) (i : ℕ) : Submodule F N :=
  Submodule.span F (b '' {j | (j : ℕ) < i})

def afLatT (p f : ℕ) {n : ℕ} (b : Module.Basis (Fin n) F N) (σ : MulChar F R)
    (M : Submodule R (N → C)) : Submodule R (Fin n × Fin f → R) :=
  (M ⊔ pFun R p N).comap (Fintype.linearCombination R
    fun (j : Fin n × Fin f) (x : N) => algebraMap R C ((σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1)))

end GlobalTheory.CompanionTheory.Ar.GR
end
end
