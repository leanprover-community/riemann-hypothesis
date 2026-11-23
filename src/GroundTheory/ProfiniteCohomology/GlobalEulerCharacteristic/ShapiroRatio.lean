module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.CardCohomologyZeroMackeyRepOfNeTop
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
  [IsDiscreteRep B]


private theorem prod_sigma_of_subtype_bijective
    {α γ : Type*} {β : α → Type*} [Fintype α] [fintypeFiber : ∀ a, Fintype (β a)] [Fintype γ]
    (p : Sigma β → Prop) [DecidablePred p] (mem : γ → {x // p x})
    (hbij : Function.Bijective mem) (f : (a : α) → β a → ℕ) (g : γ → ℕ) (n : ℕ)
    (htop : ∀ w, g w = f (mem w).1.1 (mem w).1.2)
    (hlow : ∀ x : Sigma β, ¬ p x → f x.1 x.2 = n) :
    (∏ a, ∏ b, f a b) = (∏ w, g w) * n ^ Nat.card {x // ¬ p x} := by
  have htopProd := Fintype.prod_bijective mem hbij g (fun x => f x.1.1 x.1.2) htop
  have hlowProd : (∏ x : {x // ¬ p x}, f x.1.1 x.1.2) = n ^ Nat.card {x // ¬ p x} :=
    (Finset.prod_congr rfl (fun x _ => hlow x.1 x.2)).trans <| by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
  exact (Fintype.prod_sigma' f).symm.trans <|
    (Fintype.prod_subtype_mul_prod_subtype p (fun x => f x.1 x.2)).symm.trans <|
      congrArg₂ (· * ·) htopProd.symm hlowProd

open scoped Classical in
theorem prod_gsRealH0Card_coind
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    ∏ v : {v : InfinitePlace K.1 // v.IsReal},
        gsRealH0Card S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
          ιr v =
      (∏ w : {w : InfinitePlace L.1 // w.IsReal},
          gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w) *
        Nat.card B ^ Nat.card {p : Σ v : {v : InfinitePlace K.1 // v.IsReal},
            MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
              (gsRealFamily S ιr v).toMonoidHom //
          ¬ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
            (gsRealFamily S ιr p.1).toMonoidHom p.2.out = ⊤} := by
  have hbij : Function.Bijective mem :=
    ⟨fun w w' h => (hmem w).symm.trans ((congrArg (realMemberPlace S ιr hL) h).trans (hmem w')),
      fun p => ⟨realMemberPlace S ιr hL p, realMemberPlace_injective S ιr hL (hmem _)⟩⟩
  let W := gsOpenSubgroup S hL
  let ψ := gsRealFamily S ιr
  let D (v : {v : InfinitePlace K.1 // v.IsReal}) :=
    MackeyDoubleCoset (W : Subgroup _) (ψ v).toMonoidHom
  let p (x : Sigma D) := mackeySubgroup (W : Subgroup _) (ψ x.1).toMonoidHom x.2.out = ⊤
  let f (v : {v : InfinitePlace K.1 // v.IsReal}) (d : D v) :=
    Nat.card (@cohomology _ _ _ _ _ _ _
      (isDiscreteRep_mackeyRep_continuousMonoidHom W (ψ v) B d.out) 0)
  let g (w : {w : InfinitePlace L.1 // w.IsReal}) :=
    gsRealH0Card (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL w
  have hsplit := prod_sigma_of_subtype_bijective
    (fintypeFiber := fun v => fintype_mackeyDoubleCoset W (ψ v)) p mem hbij f g (Nat.card B)
    (fun w => (card_cohomology_zero_mackeyRep_top S hL ιr B ιrL (mem w) w (e w) (he w)).symm)
    (fun x hx => card_cohomology_zero_mackeyRep_of_ne_top S hL ιr B x.1 x.2 hx)
  exact (Finset.prod_congr rfl (fun v _ => gsRealH0Card_coind S hL ιr B v)).trans hsplit

theorem ratio_coind_arith {χ χ' PK PL nC nB : ℚ} {cK cL b n : ℕ} (hχ : χ = χ') (hC : nC = nB ^ n)
    (hP : PK = PL * nB ^ b) (hN : cL + b = n * cK) (hB : nB ≠ 0) :
    χ * nC ^ cK / PK = χ' * nB ^ cL / PL := by
  subst hχ hC hP
  rw [← pow_mul, ← hN, pow_add, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero _ hB)]


private theorem rat_prod_eq_of_nat_prod_eq {α β : Type*} [Fintype α] [Fintype β]
    {f : α → ℕ} {g : β → ℕ} {n b : ℕ}
    (h : (∏ x, f x) = (∏ y, g y) * n ^ b) :
    (∏ x, (f x : ℚ)) = (∏ y, (g y : ℚ)) * (n : ℚ) ^ b := by
  simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow] using
    congrArg (fun m : ℕ => (m : ℚ)) h

theorem gsEulerRatio_coind_eq_of [Finite B]
    (ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion)
    (mem : {w : InfinitePlace L.1 // w.IsReal} → MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL))
    (hmem : ∀ w, realMemberPlace S ιr hL (mem w) = w)
    (e : ∀ w, Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion) ≃*
      Gal(AlgebraicClosure w.1.Completion / w.1.Completion))
    (he : ∀ w (g : Gal(AlgebraicClosure (mem w).1.1.1.Completion / (mem w).1.1.1.Completion))
      (hg : (mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹ ∈ gsOpenSubgroup S hL),
      gsBaseChange S hL ⟨(mem w).1.2.out * gsRealFamily S ιr (mem w).1.1 g * (mem w).1.2.out⁻¹, hg⟩ =
        decompHomS w.1.Completion (placesOver S) (ιrL w) (e w g)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B) ιr =
      gsEulerRatio (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B) ιrL := by
  have hχ := (eulerChar_coind (gsOpenSubgroup S hL) B).trans
    (eulerChar_res_continuousMulEquiv (gsBaseChange S hL).symm B).symm
  have hC := (congrArg (fun m : ℕ => (m : ℚ)) (card_coind_gsOpenSubgroup S hL B)).trans
    (Nat.cast_pow _ _)
  have hPq := rat_prod_eq_of_nat_prod_eq (prod_gsRealH0Card_coind S hL ιr B ιrL mem hmem e he)
  have hN := card_infinitePlace_add_card S hL ιr
  simp only [Nat.card_eq_fintype_card (α := InfinitePlace K.1), Nat.card_eq_fintype_card (α := InfinitePlace L.1)]
    at hN
  have hB : (Nat.card B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  exact ratio_coind_arith hχ hC hPq hN hB

end

end GroundTheory.ProfCoh
