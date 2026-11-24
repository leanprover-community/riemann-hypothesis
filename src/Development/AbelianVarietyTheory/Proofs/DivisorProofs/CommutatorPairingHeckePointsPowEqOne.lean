module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem eta_nsmul {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {M : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b M s) (y : D.La) (m : ℕ) : o.eta (m • y) = o.eta y ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem weilIs_heckeSub_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u → u ^ k = 1 := by
  intro p _ D R _ b g c k N _ _ _ _ _ _ _ S s o h₁ hh₁ h₂ _ u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨x, rfl⟩ := hh₁
  have hk1 : o.eta (N • g x) ^ k = 1 := by
    rw [← eta_nsmul, smul_smul, Nat.mul_comm k N]; exact o.eta_ker _
  have hxk : (lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (lbPow o.P (k ^ 2 / c)) 1
      ((lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 h₂) (u ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ u (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hu
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

end GlobalTheory.UPel.HT.Hecke
