module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem DifferentiableLines.nonempty_toroidal_flag_bundle : GlobalTheory.Published.ToroidalCompactification → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → Nonempty (GlobalTheory.CompHS.TorFlag Xo c) := by
  intro hP E _ _ _ H Dw l Xo c hd
  obtain ⟨Y, hs, hb, hk⟩ := hP E H Dw hd l Xo c
  exact GlobalTheory.CompHS.TorFlagEx.torFlag_of_model Y hs hb hk
    (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta Y (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw hd l Xo c Y hs))
