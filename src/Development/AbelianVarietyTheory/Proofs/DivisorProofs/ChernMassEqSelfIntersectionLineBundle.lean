module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionOfGeneratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMultilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGeneratedStatement
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.twist_ample_globally_generated Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact GlobalTheory.T.chernMass_eq_selfIntersection_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
