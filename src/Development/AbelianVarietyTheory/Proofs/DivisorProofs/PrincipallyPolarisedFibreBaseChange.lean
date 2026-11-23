module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.GtBaseChangeSharp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isPPFib_baseChange : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] (g : ℕ) (M : RigLB G), E8Fibration.IsPPFib G g M → ∃ M' : RigLB ((Over.pullback f).obj G), M'.L = M.L.pull (pullback.fst G.hom f) ∧ E8Fibration.IsPPFib ((Over.pullback f).obj G) g M' := by
  intro S S' f G _ g M hM
  obtain ⟨hA, hg, ⟨c⟩, ha, hK⟩ := hM
  have hA' : IsAbelianScheme ((Over.pullback f).obj G) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd G.hom f)
      infer_instance
    · change IsProper (pullback.snd G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd G.hom f)
      infer_instance
  have := hA.comm
  have := hA'.comm
  have := hA.proper
  have h := isGrpPullback_pullback G f
  obtain ⟨hL, hr, c', -⟩ := GlobalTheory.PullSharp.cube_pull_sharp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h) M c
  obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl hL
  exact ⟨(ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubeMapOf h).rigLB M hL hr, rfl, hA',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hg, ⟨c'⟩,
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback M.isLB ha h.1,
    kTriv_pull h M.isLB hL ((isGen_iff w).1 hw) hK⟩

end GlobalTheory.Poinc.Sep.E8Fibration

end
