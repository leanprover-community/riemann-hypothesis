module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeightStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIsoStatement
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
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernMass_lineBundleWeightOfIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight Y A _ ψ h1 hψ

end GlobalTheory
