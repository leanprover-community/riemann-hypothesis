module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderProdSubProd

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.SubstMod

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, (k i : ℕ∞) ≤ (a i).order) (hb : ∀ i ∈ s, (k i : ℕ∞) ≤ (b i).order)
    (hab : ∀ i ∈ s, (k i : ℕ∞) + 1 ≤ (a i - b i).order) :
    (∑ i ∈ s, (k i : ℕ∞)) + 1 ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order := by
  first
  | exact @_root_.GlobalTheory.OrderProductDifference.target
  | exact _root_.GlobalTheory.OrderProductDifference.target
  | (apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrderProductDifference.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrderProductDifference.target ..)

theorem order_pow_sub_pow {R τ : Type} [CommRing R] (u l : MvPowerSeries τ R)
    (hu : constantCoeff u = 0) (hl : constantCoeff l = 0) (hul : (2 : ℕ∞) ≤ (u - l).order)
    (n : ℕ) : (n : ℕ∞) + 1 ≤ (u ^ n - l ^ n).order := by
  have := order_prod_sub_prod (Finset.range n) (fun _ => u) (fun _ => l) (fun _ => 1)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hl)
    (fun _ _ => by simpa [one_add_one_eq_two] using hul)
  simpa [Finset.prod_const] using this

theorem order_monoProd_sub {R σ τ : Type} [CommRing R] (u l : σ → MvPowerSeries τ R)
    (hu : ∀ s, constantCoeff (u s) = 0) (hl : ∀ s, constantCoeff (l s) = 0)
    (hul : ∀ s, (2 : ℕ∞) ≤ (u s - l s).order) (α : σ →₀ ℕ) :
    (α.degree : ℕ∞) + 1 ≤
      ((α.prod fun s e => u s ^ e) - α.prod fun s e => l s ^ e).order := by
  have := order_prod_sub_prod α.support (fun s => u s ^ α s) (fun s => l s ^ α s) α
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hl s))
    (fun s _ => order_pow_sub_pow _ _ (hu s) (hl s) (hul s) _)
  rw [Finsupp.degree_apply]
  push_cast
  exact this

end GlobalTheory.SubstMod
