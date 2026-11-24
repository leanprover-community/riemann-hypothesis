module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
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

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem admissible_of_jet_bounds {E : Ent D} {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (z : Pl D)
    (Th : MvPowerSeries (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p])
    (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1)
    (h1 : Formalism.MainNotions.product_zeroth_first_parts.B1 p (nP D p) be) (h2 : Formalism.MainNotions.product_zeroth_first_parts.B2 p (nP D p) be) (h3 : Formalism.MainNotions.product_zeroth_first_parts.B3 p (nP D p) be)
    (h4 : Formalism.MainNotions.product_zeroth_first_parts.B4 p (nP D p) be) (h0 : OrbitThetaExpansion (orbLoc E p h u i z Th) ep sg be) :
    (orbLoc E p h u i z Th).AdmB := by
  obtain ⟨U, hU, hT⟩ := h0
  exact ⟨ep, hep, be, ⟨sg, hsg, U, hU, hT⟩, h1, h2, h3, h4⟩

theorem kvalGe_mono {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
    {nu : Lt → YoungDiagram} {Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]} {B B' : ℝ}
    (hK : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) (hB : B' ≤ B) : Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := by
  unfold Formalism.MainNotions.product_zeroth_first_parts.KvalGe at hK ⊢
  intro I m
  refine (hK I m).trans ?_
  have hl : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB)

end PI.OrbBoundFW
