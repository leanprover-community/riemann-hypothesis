module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAtCompleteTraitOfModel
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical


theorem _root_.GlobalTheory.T.exists_uniformisation_at_completeTrait_of_model : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → CharZero V → ∀ (ξ : Sp V ⟶ Y.Z) (e : X₁.Ω₁ →+* FractionRing V), jK V ≫ ξ = spMap e ≫ Y.pt → (ξ ⁻¹' abLocus O.G).Nonempty → ∃ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback ξ).obj O.G)) (β : A.A.left ⟶ ((Over.pullback Y.pt).obj O.G).left), IsGrpPullback A.A ((Over.pullback Y.pt).obj O.G) (spMap e) β ∧ LBIso A.L ((O.L.L.pull (pullback.fst O.G.hom Y.pt)).pull β) ∧ ∀ F : O.G ⟶ O.G, IsMonHom F → ∃ E : EndU U.toUnifPre, E.aA.left ≫ β = β ≫ ((Over.pullback Y.pt).map F).left := by
  first | exact @GlobalTheory.Poinc.Sep.exists_unif_trait | exact GlobalTheory.Poinc.Sep.exists_unif_trait | (intros; apply GlobalTheory.Poinc.Sep.exists_unif_trait <;> assumption)
