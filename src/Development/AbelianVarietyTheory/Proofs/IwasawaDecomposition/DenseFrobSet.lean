module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)

  simp only [heckePol, sysPol, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
  Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
