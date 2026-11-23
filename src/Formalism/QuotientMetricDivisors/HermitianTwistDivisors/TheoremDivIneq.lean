module

public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AbsorbE
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivAssembly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_inequality : TheoremDivIneq := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 Lpass Eb e6 eP logOm eK pq w eE δ
    h1 h2 h3 h4 h5 h6 h7 h8
    hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk hN hS ht hη hdC
    hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP heE hδ
  have hD := divisor_inequality_assembly J Pl TT muC mu0 Lpass 0 Fo Eb hu hP mlam e6 eP logOm logT k hK eK pq aT
    w phν nν fa eE δ h1 (by linarith) (by linarith) h4 h5 h6 h7 h8
  have hA := error_absorption J Pl TT x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 Lpass
    Eb e6 eP logOm k eK pq w eE δ hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk
    hN hS ht hη hdC hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP
    heE hδ
  rw [hJ] at hD
  linarith

end Formalism.DivisionValues
