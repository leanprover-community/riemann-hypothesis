module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter TensorProduct

namespace Formalism.AUTREP

section Inert

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

open ReciprocityTheory.Aut

structure InertDatum (v : HeightOneSpectrum (𝓞 L⁺)) (w : HeightOneSpectrum (𝓞 L)) where
  e : L ⊗[L⁺] v.adicCompletion L⁺ ≃+* w.adicCompletion L
  σw : w.adicCompletion L →+* w.adicCompletion L
  ϖ : w.adicCompletion L
  P : GL (Fin n) (w.adicCompletion L)
  comm : ∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion L⁺) x) = σw (e x)
  unram : Formalism.UG.IsUnramInv ϖ σw (Formalism.UG.qV L⁺ v)
  integ : ∀ x, x ∈ Formalism.UG.tensInt (F := L⁺) (v.adicCompletion L⁺) (Formalism.UG.intOE L) (Formalism.UG.Ov L⁺ v) ↔
    e x ∈ Formalism.UG.intL (w.adicCompletion L)
  Pint : P ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range
  Panti : Formalism.UG.cT σw (P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * (P : Matrix (Fin n) (Fin n) _) =
    Formalism.UG.antiJ (w.adicCompletion L) n

variable {L n}

def InertDatum.loc {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (x : GAf L n) : GL (Fin n) (w.adicCompletion L) :=
  D.P⁻¹ * Formalism.UG.bc (n := Fin n) (D.e : L ⊗[L⁺] v.adicCompletion L⁺ →+* w.adicCompletion L)
    (Matrix.GeneralLinearGroup.map (compAt L v) (x : GL (Fin n) (AL L))) * D.P


open Classical in
def InertDatum.hval {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (y : GL (Fin n) (w.adicCompletion L)) : ℂ :=
  if hy : y ∈ Formalism.UG.GU D.σw n then h ⟨y, hy⟩ else 0

variable (L n)


open Classical in
def heckeFunI {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (f : GAf L n → W) : GAf L n → W :=
  fun g => ∑ᶠ c : GAf L n ⧸ U,
    if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside (L := L) {v} x then
      D.hval h (D.loc hc.choose) • f (g * hc.choose) else 0


end Inert

end Formalism.AUTREP
