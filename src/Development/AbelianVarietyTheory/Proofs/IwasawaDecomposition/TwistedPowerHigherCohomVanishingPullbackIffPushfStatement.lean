module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf
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

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
