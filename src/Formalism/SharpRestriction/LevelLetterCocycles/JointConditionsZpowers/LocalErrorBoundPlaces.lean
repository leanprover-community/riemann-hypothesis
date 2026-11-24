module

public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
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

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

open Classical

variable {D : D7}

section Exp

variable (L : SizeData₂ D)

def hN : ℕ := ⌊Formalism.MainNotions.TwistedPlaces.hB L⌋₊

def eA (CA : ℝ) (l : ℕ) : ℕ :=
  ⌈CA * (1 + ((hN L + hN L : ℕ) : ℝ) / (l : ℝ) + (1 + Real.logb l (((hN L + hN L : ℕ) : ℝ) + 1)))⌉₊

end Exp

section RowA

def lenA (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  if lam ∈ dc.col then (2 * (locDeg D.host.E lam : ℚ) * D.R.m + 1) * e' else 0

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowA

section Star

variable (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def localErrorBoundPlaces (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : ℚ :=
  (∑ u ∈ dc.col, ((locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * D.nd.vdel i + 2 * D.nd.vdel i + Br.h0W i u ρ π +
      (D.R.r : ℚ) * (c0 u : ℚ))) +
    (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col

end Star

end Formalism.MainNotions.N

end
