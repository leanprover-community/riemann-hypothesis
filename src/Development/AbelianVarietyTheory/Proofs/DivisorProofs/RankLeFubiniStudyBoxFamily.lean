module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFubiniStudyRatFnsMemPairSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNefStatement
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections k X p M _ (boxFam e x) w hFS
  subst hPL
  exact GlobalTheory.T.rank_le_geometricDegree_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
