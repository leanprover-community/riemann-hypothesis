module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (Twisted SamePair SameBelow LiesUnder TwistedPlaceSettings)

theorem cond_powers {D : D7} {C : NChoice D} {I : TwIn D} (h : DQ.GoodAllAt D C I) :
    (∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (C.twI w) (C.Q w)) ∧
    ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (C.twI w) (C.Q w) (C.k' w) (C.psi' w ^ a) (twEps D (C.twI w)) := by
  classical
  refine ⟨fun w hw => ?_, I.N0, fun w hw a ha => ?_⟩
  · have h1 := ((h w hw).2 1 (by simp)).1
    exact ⟨fun P hP => (h1.1 P hP).1, (Finset.disjoint_union_right.1 h1.2.1).1,
      GlobalTheory.AntiRam.ramExactly_conj D _ _ _ h1.2.2.2.2.1 h1.2.2.2.2.2.2.1⟩
  · have e : ∃ b : ℤ, b.natAbs = a.natAbs ∧ BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w ^ b) = C.psi' w ^ a := by
      cases C.sd w
      · exact ⟨-a, Int.natAbs_neg a, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, rfl, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    have hc : Nat.Coprime b.natAbs (D.ntw.l (C.twI w)) := by
      rw [hb]
      simpa using Int.isCoprime_iff_nat_coprime.1 ha
    exact e ▸ ((h w hw).2 b hc).2.2.2.2.1

theorem twI_eq {D : D7} {C : NChoice D} {xd : ThData D} (h : GoodO D C xd) {w w' : D.what₂.places.Pl}
    (hw : Twisted D w) (hw' : Twisted D w') (e : C.Q w = C.Q w') (hne : C.Q w ≠ ∅) : C.twI w = C.twI w' := by
  by_contra hn
  have := h.sep w w' hw hw' hn
  rw [← e] at this
  exact hne (disjoint_self.1 this)

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

end GlobalTheory.Mem.LiteralAutomorphy.TwAtLink

end
