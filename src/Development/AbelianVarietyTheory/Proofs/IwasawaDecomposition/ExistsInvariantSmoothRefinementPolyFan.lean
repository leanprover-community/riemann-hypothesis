module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicityStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFanStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

theorem resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS
  suffices key : ∀ n : ℕ, ∀ φ lab : InvFun (𝓞 E), maxMult H.bar q φ = n → IsPolyFan H.bar q φ → IsTwInv H φ →
      IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧
        IsTwInv H φ' ∧ Subordinate H.bar q φ' φ by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.maxSimplicialCellMultiplicity_lt_top_of_isPolyFan E H q φ hP).ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult H.bar q φ
    · obtain ⟨φ', lab', hP', hT', hL', hS', hsub, hlt⟩ :=
        GlobalTheory.T.exists_starSubdivision_lowers_maxCellMultiplicity E H q φ lab hD hP hT hL hS (hn ▸ ENat.coe_lt_top n) h2
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
      have hkn : k < n := by
        rw [← hk, hn] at hlt; exact_mod_cast hlt
      obtain ⟨φ'', h1, h2, h3, h4⟩ := ih k hkn φ' lab' hk.symm hP' hT' hL' hS'
      exact ⟨φ'', h1, h2, h3, h4.trans hsub⟩
    · have hle : maxMult H.bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have : ¬ 2 ≤ n := fun h => h2 (by exact_mod_cast h)
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨h1, h2⟩ := GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField E H q φ lab hD hP hS hle
      exact ⟨φ, h1, h2, hT, Subordinate.refl φ⟩

end GlobalTheory.PolFan
