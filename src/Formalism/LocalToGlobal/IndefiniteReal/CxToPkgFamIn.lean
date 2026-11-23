module

public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
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

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def crdOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Crd A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A.fam.R t).toF (A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A.fam.R t).toF (A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A.fam.L j t).toF (A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A.fam.L j t).toF (A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Concrete

end Formalism.IndefR.Cx
