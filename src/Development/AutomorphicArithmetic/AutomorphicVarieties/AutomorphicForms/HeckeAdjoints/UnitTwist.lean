module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ExpoChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.OneScalar
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.unitTwist :
    UpperTheory.V.Af.Gk.UnitTwist := by
  intro F _ _ _ a ha π
  obtain ⟨s, hs⟩ := UpperTheory.V.Af.Gk.oneScalar F a π
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Af.Gk.expoChar F (-s / ((Fintype.card (InfinitePlace F) : ℂ) * a))
  refine ⟨χ, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have ht : (Matrix.of (oneL F a)).trace = (a : TR.Rinf F) := by
    change (1 : Matrix (Fin a) (Fin a) (TR.Rinf F)).trace = _
    simp
  have h1 : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hd : TR.dchi χ (Matrix.of (oneL F a)).trace = -s := by
    rw [ht, TR.dchi_eq_sum]
    simp only [hχ, Pi.natCast_apply, Complex.ofReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  change TR.lie F a (oneL F a) (TR.mulChi a χ φ) = 0
  rw [TR.lie_mulChi, hs φ hφ, hd, ← add_smul, add_neg_cancel, zero_smul, map_zero]
