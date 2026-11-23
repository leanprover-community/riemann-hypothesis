module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
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

open NumberField Neutral.B1 GlobalTheory.HeckeGal
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have hquot : χ * χ'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (χ * χ'⁻¹).1
      (χ * χ'⁻¹).2.1 (χ * χ'⁻¹).2.2 hfin.toFinset fun v hv x => ?_)
    have hl' : (l : 𝓞 E) ∉ v.asIdeal :=
      fun h => hv (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v x))
    have a := hχ.loc_away (Or.inl hl') x σ hσ.symm
    have b := hχ'.loc_away (Or.inl hl') x σ hσ.symm
    have hloc : χ.loc v x = χ'.loc v x :=
      Units.ext (ι.symm.injective (a.symm.trans b))
    change χ.loc v x * (χ'.loc v x)⁻¹ = 1
    rw [hloc, mul_inv_cancel]
  exact mul_inv_eq_one.mp hquot
