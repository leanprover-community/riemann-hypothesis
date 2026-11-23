module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.StatementLoc
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.hQuad :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ), l.Prime → 5 ≤ l → Module.finrank ℚ K = 2 → discr K = l → classNumber K < l := by
  intro K _ _ l hl h5 hn hd
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have habs : |((discr K : ℤ) : ℝ)| = (l : ℝ) := by
    rw [hd]
    push_cast
    exact abs_of_pos hl0
  rw [hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have hx0 : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hl0
  have h5r : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hx1 : Real.sqrt (l : ℝ) ≠ 1 := by
    intro h1
    have hs := Real.sq_sqrt hl0.le
    rw [h1] at hs
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hx0 hx1
  have hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l := Real.mul_self_sqrt hl0.le
  have hlt : (classNumber K : ℝ) < l := by
    calc (classNumber K : ℝ) ≤ Real.sqrt (l : ℝ) * (1 + Real.log (Real.sqrt (l : ℝ))) := h
      _ < Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hx0
        linarith
      _ = l := hsq
  exact_mod_cast hlt
