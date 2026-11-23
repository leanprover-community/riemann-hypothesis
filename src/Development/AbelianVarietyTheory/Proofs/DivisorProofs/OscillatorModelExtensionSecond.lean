module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SerAll


open NumberField Matrix Complex MeasureTheory IsDedekindDomain in
open scoped TensorProduct Classical ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.AdTh.SerAll.lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) {x : ℝ} (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) :
    _root_.Formalism.L2.Pj.lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ _root_.GlobalTheory.PtId.degW Dw a := by
  have hy : 0 < 2 * Real.pi * x := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le, ← Real.rpow_natCast, ← Real.rpow_mul hy.le,
    Real.rpow_def_of_pos hy]
  unfold _root_.Formalism.L2.Pj.lieFac _root_.GlobalTheory.PtId.degW
  congr 1
  push_cast
  ring


end GlobalTheory.AdTh.SerAll
