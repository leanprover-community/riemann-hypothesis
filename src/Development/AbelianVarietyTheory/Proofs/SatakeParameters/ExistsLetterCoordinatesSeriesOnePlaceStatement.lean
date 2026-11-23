module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlace
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  first | exact @GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | exact GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | (intros; apply GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace <;> assumption)
