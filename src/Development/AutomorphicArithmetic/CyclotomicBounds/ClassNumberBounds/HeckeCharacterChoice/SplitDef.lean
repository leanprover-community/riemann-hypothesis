import Mathlib

open NumberField

namespace KStar.Choice

def SplitsCompletely (E : Type*) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
    P.ramificationIdx ℤ = 1 ∧ P.inertiaDeg ℤ = 1










theorem SplitsCompletely.of_tower {E L : Type*} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {p : ℕ} (hp : p.Prime) (h : SplitsCompletely L p) :
    SplitsCompletely E p := by
  intro P h1 h2
  have _ := hp
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  obtain ⟨h3, h4⟩ := h Q hQ1 hQ3
  exact ⟨Nat.dvd_one.1 (h3 ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P Q),
    Nat.dvd_one.1 (h4 ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) P Q)⟩

end KStar.Choice
