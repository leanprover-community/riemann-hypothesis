module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefTens

theorem isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  intro HC k _ X _ p D hX L M NL NM
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  refine ⟨NL.semiPos.tens NM.semiPos, ?_, fun Z i _ _ _ hc hd => ?_⟩
  · intro Z i _ _ κ _ _ _ hd
    rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
    exact add_nonneg (NL.vertical Z i κ hd) (NM.vertical Z i κ hd)
  · obtain ⟨h, H⟩ := hex L
    obtain ⟨h', H'⟩ := hex M
    obtain ⟨h'', H''⟩ := hex (L.tens M)
    obtain ⟨r, hr⟩ := exists_isRatSec ((L.tens M).restr i).isLB
    obtain ⟨r₁, hr₁, h1⟩ := NL.horizontal Z i hc hd
    obtain ⟨r₂, hr₂, h2⟩ := NM.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H''.point Z i hc hd r hr,
      PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd),
      H.point Z i hc hd r₁ hr₁, H'.point Z i hc hd r₂ hr₂]
    exact add_nonneg h1 h2

end GlobalTheory.NefTens
