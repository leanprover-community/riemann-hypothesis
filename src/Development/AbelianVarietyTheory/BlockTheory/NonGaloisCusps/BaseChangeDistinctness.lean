module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness

open NumberField Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def cmTypeOf (H : Host R) : Set (H.E →+* ℂ) := H.cmType

def SphericalInert (B : NBC A) (j : ℕ) (π : B.AU j) : Prop :=
  ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

structure IsBaseChange (B : NBC A) (j : ℕ) (π : B.AU j) (Pa : List (Part A.CG)) : Prop where

  discrete : ∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d

  conjSelfDual : ∀ p ∈ Pa, A.csd p.π

  distinct : Pa.Nodup

  rank : rankIso N A Pa = R.nV

  split : ∀ w : PlE H, IsSplitPl H w → isoLoc N A Pa w = B.locAU j π w

  inert : ∀ w : PlE H, ¬ IsSplitPl H w →
    A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) = ubc R.nV (B.satAU j π w)

  inf : ∀ τ : H.E →+* ℂ, isoInf N A Pa τ = B.infW j (B.wtAU j π) τ

  inf_conj : ∀ τ ∈ cmTypeOf H,
    isoInf N A Pa (ComplexEmbedding.conjugate τ) = (B.infW j (B.wtAU j π) τ).map (fun z => -z)

def BaseChangeDefinite_at (B : NBC A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, SphericalInert B j π →
    ∃ Pa : List (Part A.CG), IsBaseChange B j π Pa

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness

end
