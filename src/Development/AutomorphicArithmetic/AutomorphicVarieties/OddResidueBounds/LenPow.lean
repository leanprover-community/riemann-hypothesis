module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem length_ker_pow_le (R X : Type) [CommRing R] [AddCommGroup X] [Module R X]
    (f : Module.End R X) (r : ℕ) :
    Module.length R (LinearMap.ker (f ^ r)) ≤ r * Module.length R (LinearMap.ker f) := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
    rw [Module.length_eq_zero_iff]
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := LinearMap.mem_ker.mp x.2
    have hy := LinearMap.mem_ker.mp y.2
    simp only [pow_zero, Module.End.one_apply] at hx hy
    rw [hx, hy]
  | succ n ih =>
    rw [pow_succ]
    refine ((UpperTheory.V.Base.lenComp R X (f ^ n) f).1).trans ?_
    calc Module.length R (LinearMap.ker (f ^ n)) + Module.length R (LinearMap.ker f)
        ≤ n * Module.length R (LinearMap.ker f) + Module.length R (LinearMap.ker f) := by
          gcongr
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length R (LinearMap.ker f) := by
          push_cast; rw [add_mul, one_mul]

theorem UpperTheory.V.Odd.lenPow :
    ∀ (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (P : Submodule R X) (a : R) (r : ℕ), (∀ x ∈ P, a ^ r • x = 0) → Module.length R P ≤ r * Module.length R (Submodule.torsionBy R X a) := by
  intro R X _ _ _ P a r hP
  let f : Module.End R X := a • (1 : Module.End R X)
  have hker : LinearMap.ker f = Submodule.torsionBy R X a := by
    ext x
    simp [f, Submodule.mem_torsionBy_iff]
  have hpow : ∀ x : X, (f ^ r) x = a ^ r • x := by
    intro x
    simp [f, smul_pow]
  have hle : P ≤ LinearMap.ker (f ^ r) := by
    intro x hx
    rw [LinearMap.mem_ker, hpow]
    exact hP x hx
  calc Module.length R P ≤ Module.length R (LinearMap.ker (f ^ r)) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ r * Module.length R (LinearMap.ker f) := length_ker_pow_le R X f r
    _ = r * Module.length R (Submodule.torsionBy R X a) := by rw [hker]
