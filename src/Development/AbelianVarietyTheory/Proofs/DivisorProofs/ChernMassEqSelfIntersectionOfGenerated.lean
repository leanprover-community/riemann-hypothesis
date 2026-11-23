module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullO1ToProjOfIsLB
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem chernInt_eq_topSelf_of_generated : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ n u hu
  have hL : L.IsLB := φ.isLB
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_dimSucc_generating_sections_infiniteField ℂ Y.X Y.str L hL Y.dim (Var.topologicalKrullDim_eq Y).le n u hu
  have hπ : ProjSpace.toProj Y.str s hs ≫ PSpace.str ℂ Y.dim = Y.str := ProjSpace.toProj_str Y.str s hs
  have e := GlobalTheory.ProjSpace.lbIso_pull_O1_toProj_of_isLB ℂ Y.dim Y.X L hL Y.str s hs
  have h1 := GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso Y _ L (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull _ hπ) φ e
    (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)).pull _ hπ) hφ
  rw [← h1, GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf Y _ hπ,
    topSelf_congr ℂ (LB.isLB_pull (ProjSpace.O1_isLB ℂ Y.dim) (ProjSpace.toProj Y.str s hs)) hL e]

end GlobalTheory
