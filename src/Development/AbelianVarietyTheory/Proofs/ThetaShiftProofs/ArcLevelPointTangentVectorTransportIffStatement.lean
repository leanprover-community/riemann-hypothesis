module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIff
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (y' : Sp ℂ⸨X⸩ ⟶ S') (y : Sp ℂ⸨X⸩ ⟶ S) (Φ' : GenPts A t' y') (Φ : GenPts A t y), w.IsGen → GenPts.Rel m w Φ' Φ → (∀ (k : ℕ) [NeZero k] (p' : Over.mk y' ⟶ t'.G) (p : Over.mk y ⟶ t.G) la, p'.left ≫ m.φ = p.left → (Φ'.LevelPt k p' la ↔ Φ.LevelPt k p la)) ∧ ∀ z₀ (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t'.G.hom y') (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y), ν' ≫ pullback.fst _ _ ≫ m.φ = ν ≫ pullback.fst _ _ → ν' ≫ pullback.snd _ _ = ν ≫ pullback.snd _ _ → (Φ'.IsTan z₀ ν' ↔ Φ.IsTan z₀ ν) := by
  first | exact @GlobalTheory.LevelTransport.levelPt_isTan_iff | exact GlobalTheory.LevelTransport.levelPt_isTan_iff | (intros; apply GlobalTheory.LevelTransport.levelPt_isTan_iff <;> assumption)
