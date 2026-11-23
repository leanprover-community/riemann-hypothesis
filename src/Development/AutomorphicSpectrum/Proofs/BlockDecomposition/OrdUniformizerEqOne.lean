module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Ad3 (Pl Qv pOf)
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

end GlobalTheory.CompanionTheory.HalfIntegral
