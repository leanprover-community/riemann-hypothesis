module

public import Formalism.LocalToGlobal.Divisibility.ZscOfNum
public import Formalism.LocalToGlobal.Divisibility.HeckeRI
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

section Scale3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def ZscOfNum3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
    (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ) (Zs : DefSub A3.fam3.amb3) : IndefScale A3.fam3.base3 where
  F0 := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).F0
  J0 := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).J0
  E1u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).E1u
  l3m := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l3m
  l3u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l3u
  l6m := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l6m
  l6u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l6u
  x := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).x
  b := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).b
  la := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).la
  de := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).de

variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
  (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ)

end Scale3

end Formalism.L2.DIV

end
