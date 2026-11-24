module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPolyRadialCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

abbrev Mb (k : ℕ) := Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ

def e0 (k r : ℕ) (X : Mb k) : Q.Mx k r := Em k r * X * (Em k r)ᵀ

def dnu (k : ℕ) (a b c : ℂ) : Mb k :=
  a • Matrix.single 0 0 1 + b • (Matrix.single 0 (Fin.last k) 1 + Matrix.single (Fin.last k) 0 1) +
    c • Matrix.single (Fin.last k) (Fin.last k) 1

def kap (T T' : ℝ) : ℂ := ((Real.sqrt T * Real.sqrt T' : ℝ) : ℂ)

def nuI (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k := nu k (star (wZ T T' ζ)) (-sZ T T' ζ)

def H1 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k 0 ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) (-(kap T T')⁻¹)

def H2 (k : ℕ) (T T' : ℝ) (ζ : ℂ) : Mb k :=
  nuI k T T' ζ * dnu k (-(kap T T')⁻¹) ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) 0

def InL (k : ℕ) (C : Mb k) : Prop := ∀ i, C i (Fin.last k) = 0 ∧ C (Fin.last k) i = 0

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
