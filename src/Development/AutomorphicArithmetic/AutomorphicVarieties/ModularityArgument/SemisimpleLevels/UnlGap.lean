module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepValuesInFiniteExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
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

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Lev.unlGap :
    UpperTheory.V.Lev.UnlGap := by
  intro F Ω _ _ _ _ _ l _ n M hM m r w hl A hA κ hκ hm i j e
  obtain ⟨χ, hχ, -, hI⟩ := hκ
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  have hψ : KillsMu M (χ j / χ i) := fun s hs => by
    rw [MonoidHom.div_apply, hχ i s hs, hχ j s hs, div_one]
  have hfin : Finite (χ j / χ i).range := (UpperTheory.galois_rep_values_in_finite_extension F Ω _ M hM _ hψ).to_subtype
  have hN : ∀ s, (χ j / χ i) s ^ Nat.card (χ j / χ i).range = 1 := fun s =>
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, s, rfl⟩ : (χ j / χ i).range)))
  have hN0 : Nat.card (χ j / χ i).range ≠ 0 := Nat.card_pos.ne'
  obtain ⟨g, hg, hne⟩ := UpperTheory.V.Ws.Pt.cycIne F Ω l A hv ((m i - (m j + 1)) * Nat.card (χ j / χ i).range)
    (mul_ne_zero (sub_ne_zero.2 (hm i j)) (by exact_mod_cast hN0))
  apply hne
  have h1 := DFunLike.congr_fun e ⟨g, Ine_le_Dec A hg⟩
  rw [MonoidHom.mul_apply, hI i _ hg, hI j _ hg] at h1
  change cycBar F Ω l g ^ m i * χ i g = cycBar F Ω l g ^ m j * χ j g * cycBar F Ω l g at h1
  have h2 : cycBar F Ω l g ^ (m i - (m j + 1)) = (χ j / χ i) g := by
    rw [MonoidHom.div_apply, zpow_sub, zpow_add_one, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h1,
      mul_right_comm, mul_comm]
  rw [zpow_mul, h2, zpow_natCast, hN]
