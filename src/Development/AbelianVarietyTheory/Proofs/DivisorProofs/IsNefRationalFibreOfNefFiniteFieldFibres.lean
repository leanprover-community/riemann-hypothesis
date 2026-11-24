module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurfaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem GlobalTheory.GenNef.isNef_ratFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  intro k _ X _ p D hX L hL
  haveI := hX.finite
  letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  refine ⟨LB.isLB_pull L.isLB _, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hzw, hpb⟩ := GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface k X p D hX Z hZ
  have e := GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber k X p Z hZ W w z hW hzw hpb L.B L.isLB
  have h0 := NefGeneric.ratDeg_nonneg k W (w ≫ p) (L.pull w rfl) hW
    (ArInt.nefFib_pull k X W p (w ≫ p) hX.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ p) (L.B.pull w) at h0
  rw [e] at h0
  exact h0
