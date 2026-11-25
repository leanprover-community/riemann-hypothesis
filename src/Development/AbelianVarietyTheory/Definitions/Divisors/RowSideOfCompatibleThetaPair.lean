module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
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

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT

open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

@[reducible] def rowSideOfCompatibleThetaPair (P : RowSideFamily ex) : IndefiniteRowSideFullHecke ex where
  Gp := P.Gp
  Pl0 := P.Pl0
  I0 := P.I0
  T := P.T
  A3 := P.A3
  P0 := P.P0
  ψ0 := P.ψ0
  Ps := P.Ps
  ψs := P.ψs
  Zs := P.Zs
  S0 := P.S0
  S1 := P.S1
  Dc := P.Dc
  Sp := P.Sp
  C := P.C
  NuC := P.NuC
  I := P.I
  JA := P.JA
  JM := P.JM
  div := P.tied.div
  amb0 := P.tied.amb0
  mjH := P.tied.mjH
  cen0 := P.tied.cen0

abbrev zscOf (P : RowSideFamily ex) (Del h0 : ℕ) (c : ℝ) : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3 :=
  (rowSideOfCompatibleThetaPair P).zsc Del h0 c

abbrev PtP : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), PtAt O.ex c → Prop

end GlobalTheory.Fc.Ind

end
