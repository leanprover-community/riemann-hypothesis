module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem twistConeVanishing_of_cut : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  intro Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩
  set φ := cutHom G hM s
  let ψ := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  let eK : kernel ψ ≅ kernel φ := (kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ
  have arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m →
      (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n) := by
    intro a n j m h₁ h₂
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h₁
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h₂
    simp only [Nat.add_sub_cancel_left]
    module
  set J := max j₁ (max jK jC) with hJ
  have hJ₁ : j₁ ≤ J := le_max_left _ _
  have hJK : jK ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : jC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p →
      Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hmj hJj p hp
      by_cases hm : m < 2 * r
      · exact h₁ j m (by omega) hm p hp
      · push_neg at hm
        have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
        have e₁ := Twist.shortExact_map hT hS₁
        have e₂ := Twist.shortExact_map hT hS₂
        obtain ⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅
            twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by
          refine nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT
            (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_
          rw [cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _),
            cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]
          exact arith _ _ j m (by omega) hm
        have hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1))
            (tens (lbPow A j) (lbPow N m))) ⊤ p) := by
          have := ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp
          exact (cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton
        have hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1)) := by
          have := hK j m (by omega) hmj (p + 1) (by omega)
          exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this
        have himg := cohOn.subsingleton₃ e₁ ⊤ p hmid hker
        exact cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)
  exact ⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩

end GlobalTheory
