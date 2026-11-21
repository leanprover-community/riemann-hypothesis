import Mathlib
import Formalism.PeriodIntegrals.GoodLatCM

section
open NumberField

namespace PI.GoodLatCMWork

open PI.GoodLatCM

def Setup (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    {S : Type} [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ) : Prop :=
  (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) ∧
  Module.finrank ℚ K = 2 ∧ NumberField.discr K = -(d : ℤ) ∧ d % 4 = 3 ∧
  Function.Injective emb ∧ (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) ∧
  Fintype.card S = Module.finrank K E ∧
  MM.FG ∧ MM ≠ ⊥ ∧
  (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) ∧
  cc ≠ ⊥ ∧ δ ≠ 0

def lam {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ) :
    AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}

def HfGFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (X Y : Matrix (Fin N') (Fin N) E),
      HfG (area (lam K φ₀ cc δ)) (fun s i j => δ * emb s (X i j)) (fun s i j => δ * emb s (Y i j)) =
        φ₀ ((Algebra.trace K E (∑ i, ∑ j, X i j * star (Y i j)) : K) : E) /
          ((Ideal.absNorm cc : ℂ) * ((Real.sqrt d / 2 : ℝ) : ℂ))

def LaBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (S → Fin N' → Fin N → ℂ)),
        gLa emb (lam K φ₀ cc δ) MM L L' = AddSubgroup.closure (Set.range b)

def LaIntegral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ y ∈ gLa emb (lam K φ₀ cc δ) MM L L',
        ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) x y).im = n

def LaSelfDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ v : S → Fin N' → Fin N → ℂ,
        (∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) v x).im = n) →
        v ∈ gLa emb (lam K φ₀ cc δ) MM L L'

def LaSemichar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ y ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ n : ℤ,
        (HfG (area (lam K φ₀ cc δ)) x y).im = n →
        alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) (x + y) =
          alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) x * alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) y *
            (-1 : ℂ) ^ n

def LaCommens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin N → E)) (L₁' L₂' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L₁ → IsSDLat E N' L₁' → IsSDLat E N L₂ → IsSDLat E N' L₂' →
      ((gLa emb (lam K φ₀ cc δ) MM L₁ L₁').addSubgroupOf (gLa emb (lam K φ₀ cc δ) MM L₂ L₂')).index ≠ 0

end PI.GoodLatCMWork
end

section
open NumberField
namespace PI.GoodLatCMWork
open PI.GoodLatCM

section Defs
variable {E : Type} [Field E] [NumberField E]

def embM {S : Type} (emb : S → E →+* ℂ) (δ : ℂ) {N N' : ℕ} (X : Matrix (Fin N') (Fin N) E) : S → Fin N' → Fin N → ℂ :=
  fun s i j => δ * emb s (X i j)

noncomputable def hh [StarRing E] (K : IntermediateField ℚ E) {N N' : ℕ} (X Y : Matrix (Fin N') (Fin N) E) : K :=
  Algebra.trace K E (∑ i, ∑ j, X i j * star (Y i j))

def cYY (K : IntermediateField ℚ E) (cc : Ideal (𝓞 K)) (MM : Submodule (𝓞 E) E) {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) : AddSubgroup (Matrix (Fin N') (Fin N) E) :=
  AddSubgroup.closure {Z | ∃ c ∈ cc, ∃ A ∈ gYY MM L L', Z = (((c : K) : E)) • A}

def matO (E : Type) [Field E] [NumberField E] (N N' : ℕ) : AddSubgroup (Matrix (Fin N') (Fin N) E) where
  carrier := {X | ∀ i j, X i j ∈ (algebraMap (𝓞 E) E).range}
  add_mem' := fun {X Y} hX hY i j => by
    rw [Matrix.add_apply]; exact add_mem (hX i j) (hY i j)
  zero_mem' := fun i j => by
    rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' := fun {X} hX i j => by
    rw [Matrix.neg_apply]; exact neg_mem (hX i j)

end Defs

def NoRealEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ → IsEmpty (K →+* ℝ)

def AreaFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    area (lam K φ₀ cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt d / 2)

def LamInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ z ∈ lam K φ₀ cc δ, ∀ w ∈ lam K φ₀ cc δ, ∃ n : ℤ, (z * (starRingEnd ℂ) w).im / area (lam K φ₀ cc δ) = n

def LamDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ v : ℂ, (∀ w ∈ lam K φ₀ cc δ, ∃ n : ℤ, (v * (starRingEnd ℂ) w).im / area (lam K φ₀ cc δ) = n) → v ∈ lam K φ₀ cc δ

def LamRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ w ∈ lam K φ₀ cc δ, ∃ c ∈ cc, w = δ * φ₀ (((c : 𝓞 K) : K) : E)

def LamMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ t : K, δ * φ₀ (t : E) ∈ lam K φ₀ cc δ → ∃ c ∈ cc, ((c : 𝓞 K) : K) = t

def OKDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ κ : K, (∀ l : 𝓞 K, ∃ n : ℤ, (φ₀ (κ : E) * (starRingEnd ℂ) (φ₀ ((l : K) : E))).im / (Real.sqrt d / 2) = n) →
      κ ∈ (algebraMap (𝓞 K) K).range

def Parity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ η : 𝓞 K, ∃ a b : ℤ, 2 * (φ₀ ((η : K) : E)).re = a ∧ (φ₀ ((η : K) : E)).im / (Real.sqrt d / 2) = b ∧ Even (a - b)

def LaEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (x : S → Fin N' → Fin N → ℂ),
      x ∈ gLa emb (lam K φ₀ cc δ) MM L L' ↔ ∃ Z ∈ cYY K cc MM L L', x = embM emb δ Z

def ResId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
    ∀ (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)), IsSDLat E N L →
      ∃ (n : ℕ) (x v : Fin n → Fin N → E), (∀ k, x k ∈ L) ∧ (∀ k, v k ∈ L) ∧ ∀ y : Fin N → E, ∑ k, stdH E N (v k) y • x k = y

def YYInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X ∈ gYY MM L L', ∀ Y ∈ gYY MM L L', hh K X Y ∈ (algebraMap (𝓞 K) K).range

def YYDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X : Matrix (Fin N') (Fin N) E, (∀ Y ∈ gYY MM L L', hh K X Y ∈ (algebraMap (𝓞 K) K).range) → X ∈ gYY MM L L'

def CInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X : Matrix (Fin N') (Fin N) E, (∀ Y ∈ gYY MM L L', ∃ c ∈ cc, ((c : 𝓞 K) : K) = hh K X Y) → X ∈ cYY K cc MM L L'

def CCInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X ∈ cYY K cc MM L L', ∀ Y ∈ cYY K cc MM L L', ∃ η : 𝓞 K, ((η : K)) * (Ideal.absNorm cc : K) = hh K X Y

def CStd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∃ m : ℕ, 0 < m ∧ (∀ Z ∈ cYY K cc MM L L', (m : E) • Z ∈ matO E N N') ∧ ∀ Z ∈ matO E N N', (m : E) • Z ∈ cYY K cc MM L L'

def StdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (S → Fin N' → Fin N → ℂ)),
      ∀ x, x ∈ AddSubgroup.closure (Set.range b) ↔ ∃ Z ∈ matO E N N', x = embM emb δ Z

def QSpan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ v : S → Fin N' → Fin N → ℂ,
        (∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) v x).im = n) →
        ∃ X : Matrix (Fin N') (Fin N) E, v = embM emb δ X

end PI.GoodLatCMWork
end
