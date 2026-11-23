module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions

structure AutTie (D : D7) (B : RowsAut) (pl : InfinitePlace B.I.F ≃ D.what₂.Tau) : Prop where
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  rd_eq : B.I.rd = D.host.rdE
  eps_eq : ∀ v (i : Fin B.I.n), B.I.ε v i = epsS D.R (Fin.cast n_eq i)
  lam_eq : ∀ v (i : Fin B.I.n), B.lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)
  ds : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)
  low : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)
  g_eq : B.g = D.host.g 0 * D.host.g 1
  g0_eq : B.g₀ = D.host.g 0
  D_eq : B.D = D.what₂.Dall
  Dstar_eq : D.what₂.Dstar =
    B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (B.w v)) B.μf B.fund B.e

end Formalism.MainNotions.S
