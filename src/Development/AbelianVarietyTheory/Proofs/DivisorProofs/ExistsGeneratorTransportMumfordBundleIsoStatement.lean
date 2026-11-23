module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_transport_mumfordBundleIso : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  first | exact @GlobalTheory.GenTransport.gen_transport | exact GlobalTheory.GenTransport.gen_transport | (intros; apply GlobalTheory.GenTransport.gen_transport <;> assumption)
