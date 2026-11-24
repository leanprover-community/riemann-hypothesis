module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOneStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivialStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeSplit

theorem heckeChar_eq_one_of_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ →
    (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  have hinf := GlobalTheory.T.heckeChar_inf_trivial_of_trivAt_degOne F E χ hχ hdeg
  have hfin := GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial F E χ hχ hdeg hinf
  ext1 x
  have hfact := (GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1).2.2 x ∅ (fun v _ => hfin v _)
  rw [hfact, hinf]
  simp

end GlobalTheory.HeckeSplit
