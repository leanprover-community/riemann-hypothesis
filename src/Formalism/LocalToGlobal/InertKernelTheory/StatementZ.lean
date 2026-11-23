module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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

noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def BeJetInt (p : ℕ) [Fact p.Prime] (be : MvPowerSeries (Fin 2) (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff be = 0 ∧
    ∀ n : Fin 2 →₀ ℕ, ((∏ x ∈ n.support, (n x).factorial : ℕ) : K0 p) * MvPowerSeries.coeff n be ∈
      Set.range (algebraMap (WW p) (K0 p))

def LowAtZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), BeJetInt p Y.be → ∀ v, ∀ j < X.mm, Y.LowAt j v 0

def Adm11OfIntegralJets : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), BeJetInt p Y.be → adm11 D X Y

def BeJetOfProp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (be : MvPowerSeries (Fin 2) (K0 p)), BeProp p be → BeJetInt p be

end Formalism.L2.KerInert
