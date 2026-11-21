import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF

section
universe u

namespace Formalism.L2.Th1.A
namespace QuadraticFlow

variable {A : Type u} [CommRing A] {D : A → A}

lemma der_add (h : IsDer D) (a b : A) : D (a + b) = D a + D b := h.1 a b

lemma der_mul (h : IsDer D) (a b : A) : D (a * b) = a * D b + b * D a := h.2 a b

lemma der_zero (h : IsDer D) : D 0 = 0 := by
  have e := h.1 0 0
  rw [add_zero] at e
  linear_combination -e

lemma der_one (h : IsDer D) : D 1 = 0 := by
  have e := h.2 1 1
  simp only [mul_one, one_mul] at e
  linear_combination -e

lemma der_neg (h : IsDer D) (a : A) : D (-a) = -D a := by
  have e := h.1 a (-a)
  rw [add_neg_cancel, der_zero h] at e
  linear_combination -e

lemma der_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, der_add h, der_neg h, ← sub_eq_add_neg]

lemma der_natCast (h : IsDer D) (n : ℕ) : D (n : A) = 0 := by
  induction n with
  | zero => simpa using der_zero h
  | succ n ih => rw [Nat.cast_succ, der_add h, ih, der_one h, add_zero]

lemma der_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  simpa using der_natCast h (OfNat.ofNat n)

lemma der_sq (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [sq, der_mul h]
  ring

lemma der_inv (h : IsDer D) {t s : A} (hts : t * s = 1) : D t = -t ^ 2 * D s := by
  have e := h.2 t s
  rw [hts, der_one h] at e
  linear_combination (-t) * e + (-D t) * hts

lemma cancel_unit {k a b : A} (hk : IsUnit k) (e : k * a = k * b) : a = b := hk.mul_left_cancel e

lemma unit_four (h6 : IsUnit (6 : A)) : IsUnit (4 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  rw [e6] at h6
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left h6
  have e4 : (4 : A) = 2 * 2 := by norm_num
  rw [e4]
  exact h2.mul h2

lemma unit_twelve (h6 : IsUnit (6 : A)) : IsUnit (12 : A) := by
  have e6 : (6 : A) = 2 * 3 := by norm_num
  have h2 : IsUnit (2 : A) := isUnit_of_mul_isUnit_left (e6 ▸ h6)
  have e12 : (12 : A) = 6 * 2 := by norm_num
  rw [e12]
  exact h6.mul h2

lemma weierstrassSubstitution_unit_fact (h6 : IsUnit (6 : A)) : IsUnit (432 : A) := by
  have e : (432 : A) = 6 * 6 * 12 := by norm_num
  rw [e]
  exact (h6.mul h6).mul (unit_twelve h6)

end QuadraticFlow

open QuadraticFlow

theorem twoTorsionTranslation : FlowTwoTorsion.{u} := by
  intro A _ W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := hC
  rw [WeierstrassCurve.Affine.equation_iff] at hE hT
  have hDt : D t = -t ^ 2 * (2 * y + W.a₁ * x + W.a₃) := by
    rw [der_inv hD ht, der_sub hD, hDxT, sub_zero, hDx]
  refine ⟨?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * hE - t ^ 2 * hT - t ^ 2 * (y - yT) * h2 +
      ((3 * xT + (x - xT) + W.a₂) + t * ((x ^ 2 + x * xT + xT ^ 2 + W.a₂ * (x + xT) + W.a₄) - W.a₁ * yT) - W.a₁ * (y - yT) * t) * ht
  · rw [hDt]
    simp only [WeierstrassCurve.b₂]
    linear_combination 4 * t ^ 4 * hE - 4 * t ^ 4 * hT + t ^ 4 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) * h2 +
      (4 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 3 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t ^ 2 * (2 + (t * (x - xT) - 1)) + 4 * t * (3 + 3 * (t * (x - xT) - 1) + (t * (x - xT) - 1) ^ 2)) * ht
  · rw [hDt]
    simp only [der_neg hD, der_mul hD, der_add hD, der_sq hD, der_ofNat hD, hDx, hDy, hDt, ha1, ha3,
      WeierstrassCurve.b₂]
    linear_combination 8 * t ^ 3 * hE - 8 * t ^ 3 * hT +
      (2 * t ^ 3 * ((2 * yT + W.a₁ * xT + W.a₃) + 2 * W.a₁ * (x - xT)) - W.a₁ * t ^ 2) * h2 +
      (8 * (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * t ^ 2 + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) * t * (3 + 2 * (t * (x - xT) - 1)) + 12 + 18 * (t * (x - xT) - 1) + 8 * (t * (x - xT) - 1) ^ 2) * ht

theorem twoTorsionTranslationWeierstrassForm : FlowTwoTorsionWp.{u} := by
  intro A _ W D x y xT yT t c g2 g3 kap hD hC hF hT hDxT hDyT h2 ht h6 hc hg2 hg3 hk
  have H1 := twoTorsionTranslation A W D x y xT yT t hD hC hF hT hDxT hDyT h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at hT
  have hkap : kap = (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) := by
    apply cancel_unit ((unit_four h6).mul (unit_twelve h6))
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.c₄] at hc hg2
    linear_combination 12 * hk + (24 * xT + 12 * c + (W.a₁ ^ 2 + 4 * W.a₂)) * hc - hg2 + 24 * W.a₁ * h2
  have ha : 4 * (xT + c) ^ 3 - g2 * (xT + c) - g3 = 0 := by
    apply cancel_unit (weierstrassSubstitution_unit_fact h6)
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.c₄,
      WeierstrassCurve.c₆] at hc hg2 hg3
    linear_combination ((12 * xT + 12 * c) ^ 2 + (12 * xT + 12 * c) * (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) + (12 * xT + (W.a₁ ^ 2 + 4 * W.a₂)) ^ 2 - 3 * ((W.a₁ ^ 2 + 4 * W.a₂) ^ 2 - 24 * (2 * W.a₄ + W.a₁ * W.a₃))) * hc - 36 * (xT + c) * hg2 -
      2 * hg3 + 432 * (2 * yT + W.a₁ * xT + W.a₃) * h2 - 1728 * hT
  have hd : D t ^ 2 = 4 * t * (1 + 3 * (xT + c) * t + kap * t ^ 2) := by
    linear_combination H1.2.1 - t ^ 2 * hc - 4 * t ^ 3 * hkap
  refine ⟨ha, hkap, ?_, hd, ?_⟩
  · rw [H1.1, hkap]
    ring
  · intro e2 e3 hs he
    linear_combination hd + (4 * t ^ 2 + 8 * (xT + c) * t ^ 3) * hs + t ^ 3 * hk - t ^ 3 * he

end Formalism.L2.Th1.A
end

section
universe u

namespace Formalism.L2.Th1.A
namespace CubicFlow

open QuadraticFlow

variable {A : Type u} [CommRing A]

def gE (W : WeierstrassCurve A) (z v : A) : A :=
  z ^ 3 + W.a₁ * z * v + W.a₂ * z ^ 2 * v + W.a₃ * v ^ 2 + W.a₄ * z * v ^ 2 + W.a₆ * v ^ 3 - v

def k3 (W : WeierstrassCurve A) (l : A) : A := 1 + W.a₂ * l + W.a₄ * l ^ 2 + W.a₆ * l ^ 3
def k2 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * l + W.a₂ * n + W.a₃ * l ^ 2 + 2 * W.a₄ * l * n + 3 * W.a₆ * l ^ 2 * n
def k1 (W : WeierstrassCurve A) (l n : A) : A :=
  W.a₁ * n + 2 * W.a₃ * l * n + W.a₄ * n ^ 2 + 3 * W.a₆ * l * n ^ 2 - l
def k0 (W : WeierstrassCurve A) (n : A) : A := W.a₃ * n ^ 2 + W.a₆ * n ^ 3 - n

lemma gE_line (W : WeierstrassCurve A) (l n z : A) :
    gE W z (l * z + n) = k3 W l * z ^ 3 + k2 W l n * z ^ 2 + k1 W l n * z + k0 W n := by
  unfold gE k3 k2 k1 k0
  ring

lemma gE_line_der (W : WeierstrassCurve A) (l n z : A) :
    fuAt W z (l * z + n) - l * fwAt W z (l * z + n)
      = 3 * k3 W l * z ^ 2 + 2 * k2 W l n * z + k1 W l n := by
  unfold fuAt fwAt k3 k2 k1
  ring

lemma wEq_iff (W : WeierstrassCurve A) (z v : A) : WEq W z v ↔ gE W z v = 0 := by
  unfold WEq gE
  constructor <;> intro h <;> linear_combination -h

lemma der_gE {D : A → A} (hD : IsDer D) {W : WeierstrassCurve A} (hC : ConstCurve D W) (z v : A) :
    D (gE W z v) = fuAt W z v * D z - fwAt W z v * D v := by
  obtain ⟨hadd, hmul⟩ := hD
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  have hsub : ∀ a b, D (a - b) = D a - D b := by
    intro a b
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  have hp2 : ∀ a, D (a ^ 2) = 2 * a * D a := fun a => by rw [sq, hmul]; ring
  have hp3 : ∀ a, D (a ^ 3) = 3 * a ^ 2 * D a := fun a => by
    rw [show a ^ 3 = a * a ^ 2 by ring, hmul, hp2]; ring
  unfold gE fuAt fwAt
  simp only [hsub, hadd, hmul, hp2, hp3, c1, c2, c3, c4, c6]
  ring

lemma cubic_roots [IsDomain A] {C3 C2 C1 C0 z1 z2 z3 : A} (hz : z1 ≠ z2)
    (h1 : C3 * z1 ^ 3 + C2 * z1 ^ 2 + C1 * z1 + C0 = 0)
    (h2 : C3 * z2 ^ 3 + C2 * z2 ^ 2 + C1 * z2 + C0 = 0)
    (he1 : C3 * (z1 + z2 + z3) + C2 = 0) :
    C3 * z3 ^ 3 + C2 * z3 ^ 2 + C1 * z3 + C0 = 0 ∧
      C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 ∧ C3 * (z1 * z2 * z3) + C0 = 0 := by
  have hq : (z1 - z2) * (C3 * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + C2 * (z1 + z2) + C1) = 0 := by
    linear_combination h1 - h2
  have hq' := (mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr hz)
  have e2 : C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 := by
    linear_combination -hq' + (z1 + z2) * he1
  have e3 : C3 * (z1 * z2 * z3) + C0 = 0 := by
    linear_combination h1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3

end CubicFlow

open QuadraticFlow CubicFlow

theorem flowThirdPoint : FlowThird.{u} := by
  intro A _ _ W D u1 w1 u2 w2 l n u3 hD hC hF hW2 hDu2 hDw2 hl hn hsum hk3 h12 h31 h32
  obtain ⟨hW1, hDu1, hDw1⟩ := hF
  have hD' := hD
  obtain ⟨hadd, hmul⟩ := hD'
  have hw1 : w1 = l * u1 + n := by linear_combination -hn
  have hw2 : w2 = l * u2 + n := by linear_combination hl - hn
  have r1 : k3 W l * u1 ^ 3 + k2 W l n * u1 ^ 2 + k1 W l n * u1 + k0 W n = 0 := by
    rw [← gE_line, ← hw1]; exact (wEq_iff W u1 w1).1 hW1
  have r2 : k3 W l * u2 ^ 3 + k2 W l n * u2 ^ 2 + k1 W l n * u2 + k0 W n = 0 := by
    rw [← gE_line, ← hw2]; exact (wEq_iff W u2 w2).1 hW2
  have hs : k3 W l * (u1 + u2 + u3) + k2 W l n = 0 := hsum
  have hk : k3 W l ≠ 0 := hk3
  obtain ⟨r3, e2, -⟩ := cubic_roots h12 r1 r2 hs
  have hD0 : D 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hDline : ∀ z, D (l * z + n) = l * D z + z * D l + D n := by
    intro z; rw [hadd, hmul]

  have T1 : u1 * D l + D n = 3 * k3 W l * u1 ^ 2 + 2 * k2 W l n * u1 + k1 W l n := by
    have h := hDline u1
    rw [← hw1, hDw1, hDu1] at h
    have hd := gE_line_der W l n u1
    rw [← hw1] at hd
    linear_combination hd - h
  have T2 : u2 * D l + D n = 0 := by
    have h := hDline u2
    rw [← hw2, hDw2, hDu2] at h
    linear_combination -h
  have hq : (u1 - u2) * (D l - k3 W l * (u1 - u3)) = 0 := by
    linear_combination T1 - T2 + 2 * u1 * hs - e2
  have hDl := sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr h12))
  have hg3 : gE W u3 (l * u3 + n) = 0 := by rw [gE_line]; exact r3
  have hd3 := der_gE hD hC u3 (l * u3 + n)
  rw [hg3, hD0, hDline] at hd3
  have hd3' := gE_line_der W l n u3
  have hK : k3 W l * (u3 - u1) * (u3 - u2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hk (sub_ne_zero.mpr h31)) (sub_ne_zero.mpr h32)
  have hkey : (k3 W l * (u3 - u1) * (u3 - u2)) * (D u3 + fwAt W u3 (l * u3 + n)) = 0 := by
    linear_combination -hd3 - D u3 * hd3' - D u3 * (2 * u3 * hs - e2)
      + fwAt W u3 (l * u3 + n) * (u3 - u2) * hDl + fwAt W u3 (l * u3 + n) * T2
  have hX : D u3 = -fwAt W u3 (l * u3 + n) := by
    have := (mul_eq_zero.mp hkey).resolve_left hK
    linear_combination this
  refine ⟨(wEq_iff W u3 _).2 hg3, hX, ?_⟩
  rw [hDline]
  linear_combination l * hX + hd3' + 2 * u3 * hs - e2 + (u3 - u2) * hDl + T2

end Formalism.L2.Th1.A
end
