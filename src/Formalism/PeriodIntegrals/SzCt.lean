module

public import Formalism.LocalRingCardinality.DataErr
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.ElevenLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.SzCt

open Formalism.BasicNotions Formalism.MainNotions.G

def Uni (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Prop :=
  L.sc.eps = eps ∧ L.Ct = Ct ∧ L.CGam = CGam ∧ L.Cc = Cc ∧ D.host.CT2 = CT2 ∧
    [P.CkLow, P.Ck6, P.CfL, P.cLL, P.CnW, P.Crho, P.CDelG, P.CLw,
      P.Cj0, P.Cw, P.cw, P.CDel, P.CCount, P.Ch0r, P.Ch0k, P.Ch0N,
      P.Cgap, P.CetaF, P.CY, P.CYL, P.Cpde, P.CccK, P.CF] = PK

def SzCt : Prop :=
  ∀ (eps Ct CGam Cc CT2 : ℝ) (PK : List ℝ), ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L),
    Uni eps Ct CGam Cc CT2 PK D L P → x0 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    ∀ j ∈ SizeData₂.lifts D, ∀ u : D.what₂.Word,
      ∑ t : HH D, ctD D u j t ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b + 2 * (D.R.f : ℝ) * D.R.k * L.sc.b'

end PI.SzCt
