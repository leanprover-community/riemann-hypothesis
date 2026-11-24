module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
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
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ExistsWittSeriesInverseFormalGroupIso

@[expose] public section

noncomputable section

namespace GlobalTheory.BeCoefficients

open Formalism.MainNotions.FormalGroupSystem
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC)

theorem beCoef : Formalism.L2.KerInert.BeCob.BeCoef := by
  apply _root_.Formalism.L2.KerInert.BeCob.beta_coefficients <;> assumption

end GlobalTheory.BeCoefficients
