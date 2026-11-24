module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LamF

theorem exists_kronecker_logOm_re (E : Type) [Field E] [NumberField E] {d d' : ℕ} (h : d' = d) [Fact d.Prime]
    [NeZero d] (hd : d % 4 = 3) :
    ∃ (_ : NeZero d') (χ : DirichletCharacter ℂ d'), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
        (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 /
          DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) 1).re := by
  subst h
  exact ⟨inferInstance, _, isKroneckerChar_quadraticChar hd, by
    rw [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]⟩

theorem exists_kronecker_logOm_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D,
    ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d),
      IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  intro D Q hp large₂
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd : D.host.d % 4 = 3 := by
    have := Q.H.d_mod
    rw [hp.1] at this
    omega
  obtain ⟨i, χ, hχ, e⟩ := exists_kronecker_logOm_re D.host.E hp.1 hd
  refine ⟨i, χ, hχ, e.trans ?_⟩
  have hv : 2 * Real.pi / rootDiscr D.host.E = Real.pi / D.host.v := by
    rw [Formalism.BasicNotions.Host.v, Formalism.BasicNotions.Host.rdE, rootDiscr_def, Int.cast_abs, one_div, div_div_eq_mul_div, mul_comm]
  rw [hv, SizeData₂.logOm, large₂.logDerivative_at_one_eq]
  rfl

end GlobalTheory.LamF
