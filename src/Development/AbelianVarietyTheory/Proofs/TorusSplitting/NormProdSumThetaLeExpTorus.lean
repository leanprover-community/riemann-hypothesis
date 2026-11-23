module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem norm_prod_sum_theta_le_exp_of_card :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : I2.PT E) (DF : ℕ) (P : I2.Par T DF) (R i N : ℕ), 2 ≤ R → 1 ≤ N → ∀ s ∈ T.Sec 1 1, T.l2 1 s = 1 → ∀ (G J : Type) [Fintype G] [Fintype J], Fintype.card G = 2 * R ^ 4 * i → Fintype.card J ≤ R ^ (2 * I2.PT.f E * T.r ^ 2) → ∀ (cf : J → ℤ) (w : G → J → Fin T.r → ℂ) (a : G → J → Fin T.r → I2.Vsp T.dim), (∀ j, |cf j| ≤ N) → (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) → (∀ g j, ∀ x ∈ T.L, ∃ c : Fin T.r → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) → (∀ g j b, ‖w g j b‖ = Real.sqrt (T.ptN2 1 s fun _ => a g j b)) → ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤ Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E T.r P.q P.m R N)) := by
  intro E _ _ _ T DF P R i N hR hN s hs hl G J _ _ hG hJ cf w a hcf ha hsp hw
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [I2.PT.l2, I2.PT.ptN2] at hl
  let eG : Fin (2 * R ^ 4 * i) ≃ G := (Fintype.equivFinOfCardEq hG).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have key := GlobalTheory.norm_prod_sum_theta_le_exp I2.T_holds E T DF P R hR s hs hs0 i N
    (Fintype.card J) hN hJ (fun _ t => (cf (eJ t) : ℂ)) (fun k t => ∏ b, w (eG k) (eJ t) b)
    (fun k t => a (eG k) (eJ t))
    (fun _ t => by
      rw [Complex.norm_intCast]
      exact_mod_cast hcf (eJ t))
    (fun k t => ⟨ha _ _, hsp _ _⟩)
    (fun k t => by
      rw [norm_prod]
      simp [hw, hl])
  have h1 : ∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b =
      ∏ k, ∑ t, (cf (eJ t) : ℂ) * ∏ b, w (eG k) (eJ t) b := by
    rw [← eG.prod_comp]
    exact Finset.prod_congr rfl fun k _ => (eJ.sum_comp _).symm
  rw [h1, neg_mul]
  exact key

end GlobalTheory
