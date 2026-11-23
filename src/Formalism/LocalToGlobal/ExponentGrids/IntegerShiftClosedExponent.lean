module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.QuotientMetricDivisors.Complement2Normaliser

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K]

def PerBd [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df.Mt t, Dc.Pt u t φ F = 0 ∨ s ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def colRhs {J : Type} (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(∑ j ∈ s, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ)


end Defs

end Formalism.AtG
