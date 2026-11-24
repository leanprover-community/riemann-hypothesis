module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem weight_scalar_zero_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  intro R _ _ Q O _ _ _ oa Y S _ φ x x' c _ h
  have e : unitOn (c 0) = unitOn (1 : Sˣ) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext (X := (Over.mk (spMap φ)).left) (V := ⊤) fun y _ => ?_
    choose J hJ using fun ψ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart Q.P.isLB (ψ y)
    have hG : Good Q.P.L y J := hJ
    have h0 := h 0 y J hG
    rw [val_corr hG (Y.Φ _ x').s_zero, val_corr hG (Y.Φ _ x).s_zero, val_one, _root_.mul_one] at h0
    have h1 : unitOn (1 : Sˣ) = 1 := map_one _
    exact h0.symm.trans ((congrArg (gm _ y ⊤) h1).trans (map_one _)).symm
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    (congrArg Units.val e))

end GlobalTheory.Heat
