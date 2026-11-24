module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T) : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i t)

def IsLiftV (i : Fin D.R.m) (t : T) (g : G) (κ : (levV R i t).Q) : Prop :=
  rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf (Vc D i)) : GL _ _)) = R.eG g

def IsAlgV (i : Fin D.R.m) (t : T) (c : G → ℂ) (κ : G → (levV R i t).Q) (x y : (R.HV i t).H) : Prop :=
  (R.HV i t).e y = ∑ g, c g • Bridge.g0Act (levV R i t).ch (κ g) ((R.HV i t).e x)

def algW (i : Fin D.R.m) (c : G → ℂ) : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG c)

theorem algW_eC (i : Fin D.R.m) :
    algW R i (RealDat.eC (A := A) (sg0 D A)) = postOn _ (R.eWf i (sg0 D A)) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups

end
