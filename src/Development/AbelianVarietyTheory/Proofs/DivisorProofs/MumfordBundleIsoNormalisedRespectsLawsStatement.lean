module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
