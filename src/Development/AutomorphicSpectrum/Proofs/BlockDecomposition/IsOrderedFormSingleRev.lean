module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.OneTermOrder

theorem nabs_unifU_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : nabs k (Zls.unifU k) < 1 := by
  rw [nabs_uniformiser (Zls.irreducible_unif (k := k)) (x := Zls.unifU k) rfl]
  have hq : 1 < resCard k := Finite.one_lt_card
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq)

theorem norm_absPow_natCast (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (j : ℕ) :
    ‖((absPow k (j : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ j := by
  rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (nabs_pos' k t).le]

theorem isOrderedForm_single_rev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsUnram (ξ i)),
    PositivityTheory.SphericalProduct.AbsAnti (PositivityTheory.SphericalProduct.atUnif k ξ) →
    IsOrderedForm (fun i : Fin n => Segment.single (IrrGL.ofChar (ξ (Fin.rev i))
      (isSmoothChar_of_isUnram (hξ (Fin.rev i)))) (IrrGL.isCusp_ofChar _ _)) (PositivityTheory.SphericalProduct.msOne ξ hξ) := by
  intro k _ _ _ _ n ξ hξ hanti
  refine ⟨?_, fun i j hij hp => ?_⟩
  · have h := Multiset.map_univ_val_equiv (Fin.revPerm (n := n))
    rw [PositivityTheory.SphericalProduct.msOne]
    conv_rhs => rw [← h, Multiset.map_map]
    rfl
  · obtain ⟨-, m, hm, he⟩ := hp
    have he' : IrrGL.ofChar (ξ (Fin.rev j)) (isSmoothChar_of_isUnram (hξ (Fin.rev j))) =
        (IrrGL.ofChar (ξ (Fin.rev i)) (isSmoothChar_of_isUnram (hξ (Fin.rev i)))).nu (m : ℂ) := he
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at he'
    have hle : ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ ≤ ‖((ξ (Fin.rev j) (Zls.unifU k) : ℂˣ) : ℂ)‖ :=
      hanti (Fin.rev_le_rev.2 hij.le)
    rw [he', MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_natCast] at hle
    have hpos : 0 < ‖((ξ (Fin.rev i) (Zls.unifU k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have hlt : nabs k (Zls.unifU k) ^ m < 1 :=
      pow_lt_one₀ (nabs_pos' k _).le (nabs_unifU_lt_one k) hm.ne'
    nlinarith

end GlobalTheory.CompanionTheory.OneTermOrder
