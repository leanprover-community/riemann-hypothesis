module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Br.minNew :
    UpperTheory.V.Br.MinNew := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hN hk χ g
    by_cases hnew : ∀ (M' : ℕ), M' ∣ N → M' ≠ N →
        ∀ (g' : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M')) ↑k)
          (χ' : DirichletCharacter ℂ M'), HasChar k χ' ⇑g' →
          (∀ᶠ (p : ℕ) in Filter.cofinite, Nat.Prime p → IsEigAt k χ' (⇑g') p (coef (⇑g.f) p)) → g' = 0
    · refine ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g.f, χ, g.char, g.one,
        fun p hp _ => g.eig p hp, hnew⟩, hN, g, rfl, Filter.Eventually.of_forall fun _ _ => rfl⟩
    · push_neg at hnew
      obtain ⟨M', hdvd, hne, g', χ', hc, hev, hg0⟩ := hnew
      have hM0 : M' ≠ 0 := by
        rintro rfl
        exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hdvd)
      haveI : NeZero M' := ⟨hM0⟩
      have hlt : M' < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hne
      obtain ⟨g'', hg''⟩ := UpperTheory.V.Br.eigEx M' k hk χ' g' hc hg0 (coef (⇑g.f))
      obtain ⟨f, hf, h, hhf, hha⟩ := ih M' hlt k hk χ' g''
      refine ⟨f, hf, h, hhf, ?_⟩
      filter_upwards [hha, hev] with p h1 h2 hp
      rw [h1 hp, hg'' p hp (h2 hp)]
      rfl
