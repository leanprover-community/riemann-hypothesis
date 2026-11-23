module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointNumbers.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (r : ℕ) (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ),
    (∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g)) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g)) ∧
    (∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
          (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a))))

end GroundTheory.Heights₂.Heights.NumbersDVR
