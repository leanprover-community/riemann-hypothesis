module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.QuotAcycCut

def ProdAcyc : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] (n : ℕ) (R : Fin n → Type) [∀ k, CommRing (R k)],
  Nonempty (A ≃+* ∀ k, R k) → (∀ k, Acyc q (sp (R k))) → Acyc q (sp A)

def Hens : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    IsUnit (q : c.pt) ∧ ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

theorem goal_of (hP : ProdAcyc) (hH : Hens) : LateralTheory.E.t_E2Cut.QuotAcyc := by
  intro H q B _ _ I hB hq
  obtain ⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩ := hH q B I hB hq

  have hst : ∀ j, Acyc q (sp (D.obj j)) := by
    intro j
    obtain ⟨m, R, _, hR, hiso⟩ := hD j
    refine hP H q (D.obj j) m R hiso fun k => ?_
    have := (hR k).1
    exact H.b5 q (R k) (hR k).2.1 (hR k).2.2

  have hC : Acyc q (sp c.pt) := by
    intro n i hn
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ x : Ht q (sp c.pt) n i, x = 0 := by
      intro x
      obtain ⟨j, y, rfl⟩ := (H.b1 q D c hc n i).1 x hqc
      have := hst j n i hn
      rw [Subsingleton.elim y 0, map_zero]
    rw [h0 x, h0 y]

  have hCK : Acyc q (sp (c.pt ⧸ K)) := by
    intro n i hn
    have := hC n i hn
    have hE := H.e1 q c.pt K hqc i n
    exact hE.2.subsingleton
  exact hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK

end LateralTheory.E.QuotAcycCut
