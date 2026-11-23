module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevel
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.classSumTerms_invariant_principalLevel : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  first | exact @GlobalTheory.PrincClassSum.terms_inv | exact GlobalTheory.PrincClassSum.terms_inv | (intros; apply GlobalTheory.PrincClassSum.terms_inv <;> assumption)
