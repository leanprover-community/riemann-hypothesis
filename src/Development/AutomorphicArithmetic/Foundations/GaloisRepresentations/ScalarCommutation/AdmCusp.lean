module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IwahoriRegularSeparable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCompactCharacterVanishing
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSliceAlt
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm :
    UpperTheory.Gal.Spc.AdmCusp := by
  intro X _ k _ _ _ _ _ _ _ n Ty hJo hJc hker hcusp f hf h hh
  have hform : ∀ g, f (Ty.L.loc g * h) = UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ g * f h := by
    intro g
    unfold UpperTheory.Gal.W2.Seed.tyFn
    split_ifs with hg
    · rw [Ty.L.comm g h hh]
      exact hf.2.2 ⟨g, hg⟩ h
    · rw [zero_mul]
      by_contra hne
      apply hg
      have hmem := hf.2.1 _ hne
      rwa [map_mul, Ty.L.pr_loc, hh, mul_one] at hmem
  have hTC : GlobalTheory.Block5c.TypeCusp := GlobalTheory.typeFunction_constantTerm_eq_zero
  have hT := hTC k (Fin n) Ty.J hJo hJc Ty.ψ hker
    (fun a b e ha hb u hu h₀ =>
      UpperTheory.Gal.Spc.typeSlice k n Ty.J hJo hJc Ty.ψ hker hcusp a b e ha hb u hu h₀)
    (UpperTheory.Gal.W2.Seed.tyFn Ty.J Ty.ψ)
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
    (fun g hg => by simp [UpperTheory.Gal.W2.Seed.tyFn, hg])
  intro a b ε ha hb μ hμ u hu g₀ h₀
  have hz := hT.2.2.2 a b ε ha hb μ hμ u hu g₀ h₀
  simp_rw [hform]
  rw [MeasureTheory.integral_mul_const, hz, zero_mul]
