module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {B N P : LB X}

theorem IsNef.topSelf_le_of_cls_eq_add (h : Published.NefProductNonneg)
    (hp : IsProjOver (strHom k (X := X))) {D : ℕ} (hD : topologicalKrullDim X = D)
    (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : topSelfIntersection k B D ≤ topSelfIntersection k P D := by
  classical
  have hf := algebraMap_eq_strHom k X
  have hS : QCoh.suppDim (structureModule X) ≤ D := by
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le X _).trans hD.le
  have hV := diffVanish_chiPic_of_isProjOver hf (structureModule X) hp hS
  have hL : ∀ j : Fin 2, ((![B, N] : Fin 2 → LB X) j).IsLB := by
    intro j; fin_cases j
    · exact hB.isLB
    · exact hN.isLB
  have hQ : ∀ _ : Fin D, P.IsLB := fun _ => hP
  have hexp := hV.interNum_of_cls_eq_sum hL hQ (fun _ _ => (1 : ℤ)) (by
    intro _
    simp [Fin.sum_univ_two, e])
  have hnn : ∀ a : Fin D → Fin 2, 0 ≤ interNum k (structureModule X) ((![B, N] : Fin 2 → LB X) ∘ a) := by
    intro a
    refine h.interNum_nonneg hp hD ?_
    intro i
    show IsNef k (![B, N] (a i))
    generalize a i = j
    fin_cases j
    · exact hB
    · exact hN
  rw [topSelf_def, topSelf_def, hexp]
  simp only [Finset.prod_const_one, one_mul]
  have h0 := Finset.single_le_sum (fun a _ => hnn a) (Finset.mem_univ (fun _ : Fin D => (0 : Fin 2)))
  exact h0

theorem IsBig.of_cls_eq_add_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) (hP : P.IsLB)
    (e : cls P hP = cls B hB.isLB + cls N hN.isLB) : IsBig k P := by
  obtain ⟨D, hD, -⟩ := hb.growth
  have hf := algebraMap_eq_strHom k X
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  have hTn : IsNef k (CechPic.tens B N) := IsNef.tens_of_isProjOver hB hN hp
  have hPn : IsNef k P := hTn.of_cls_eq hP (by rw [e, CechPic.cls_tens hB.isLB hN.isLB])
  have hle := IsNef.topSelf_le_of_cls_eq_add h.1 hp hD hB hN hP e
  have hpos : 0 < topSelfIntersection k B D := (h.2.2.isBig_iff hp hD hB).1 hb
  exact (h.2.2.isBig_iff hp hD hPn).2 (lt_of_lt_of_le hpos hle)

theorem IsBig.tens_nef (h : Published.NefNumerics) (hp : IsProjOver (strHom k (X := X)))
    (hb : IsBig k B) (hB : IsNef k B) (hN : IsNef k N) : IsBig k (CechPic.tens B N) := by
  have hT : (CechPic.tens B N).IsLB := CechPic.isLB_tens hB.isLB hN.isLB
  exact IsBig.of_cls_eq_add_nef h hp hb hB hN hT (CechPic.cls_tens hB.isLB hN.isLB hT)

theorem IsNef.isBig_tens_ample [IsIntegral X] (h : Published.NefNumerics)
    (hp : IsProjOver (strHom k (X := X))) (hN : IsNef k N) (hB : IsAmpleLB B) :
    IsBig k (CechPic.tens N B) := by
  have hT : (CechPic.tens N B).IsLB := CechPic.isLB_tens hN.isLB hB.isLB
  have hbig : IsBig k B := IsAmpleLB.isBig k X hp B hB
  exact IsBig.of_cls_eq_add_nef h hp hbig hB.isNef hN hT
    (by rw [CechPic.cls_tens hN.isLB hB.isLB hT, add_comm])

theorem IsNef.isPsEff : Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ N : LB X, IsNef k N → IsPsEff N := by
  intro h k _ X _ _ hp N hN
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  refine ⟨hN.isLB, A, hA, fun m hm => ?_⟩
  have hNm : IsNef k (lbPow N m) := hN.pow hA m
  have hbig : IsBig k (CechPic.tens (lbPow N m) A) := IsNef.isBig_tens_ample h hp hNm hA
  obtain ⟨r, hr, hs⟩ := (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
  exact ⟨r, hs, hr⟩

end GlobalTheory
