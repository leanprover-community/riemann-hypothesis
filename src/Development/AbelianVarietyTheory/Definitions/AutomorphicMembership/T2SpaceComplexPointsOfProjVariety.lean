module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped TensorProduct

namespace GlobalTheory.ProjVar

variable {F : Type} [Field F]

def CxExt (σ : F →+* ℂ) (A : Type) [CommRing A] [Algebra F A] : Type :=
  letI := σ.toAlgebra
  ℂ ⊗[F] A

namespace CxExt

variable (σ : F →+* ℂ) {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

def Tensor (F : Type) [Field F] [Algebra F ℂ] (A : Type) [CommRing A] [Algebra F A] : Type := ℂ ⊗[F] A

instance {_ : Algebra F ℂ} : CommRing (Tensor F A) := inferInstanceAs (CommRing (ℂ ⊗[F] A))

instance {_ : Algebra F ℂ} : Algebra ℂ (Tensor F A) := inferInstanceAs (Algebra ℂ (ℂ ⊗[F] A))

instance : CommRing (CxExt σ A) :=
  inferInstanceAs (CommRing (@Tensor F _ σ.toAlgebra A _ _))

instance : Algebra ℂ (CxExt σ A) :=
  inferInstanceAs (Algebra ℂ (@Tensor F _ σ.toAlgebra A _ _))

def of : A →+* CxExt σ A :=
  letI := σ.toAlgebra
  (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := A)).toRingHom

variable {σ} in
def lift {B : Type} [CommRing B] [Algebra ℂ B] (φ : A →+* B)
    (h : ∀ a, φ (algebraMap F A a) = algebraMap ℂ B (σ a)) : CxExt σ A →ₐ[ℂ] B :=
  letI := σ.toAlgebra
  letI : Algebra F B := ((algebraMap ℂ B).comp σ).toAlgebra
  haveI : IsScalarTower F ℂ B := .of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId ℂ B) ({ φ with commutes' := h } : A →ₐ[F] B)
    fun _ _ => Commute.all _ _

def map (f : A →ₐ[F] A') : CxExt σ A →ₐ[ℂ] CxExt σ A' :=
  lift ((of σ).comp f.toRingHom) fun a => (congrArg (of σ) (f.commutes a)).trans (of_algebraMap σ a)

end CxExt

namespace Var

variable (Y : Var F) (σ : F →+* ℂ)

abbrev pts : Type := CxPts Y.str σ

instance secondCountable_pts : SecondCountableTopology (Y.pts σ) :=
  CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver

instance t2Space_complexPointsOfProjVariety : T2Space (Y.pts σ) := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver

abbrev an : AnRead Y.str σ Y.dim := AnRead.all Y.str σ Y.dim

abbrev FnC : Type := CxExt σ Y.Fn

def cx : Y.Fn →+* Y.FnC σ := CxExt.of σ

instance algebraStalk (x : Y.X) : Algebra F (Y.X.presheaf.stalk x) :=
  ((Y.X.presheaf.germ ⊤ x trivial).hom.comp (algX Y.str ⊤)).toAlgebra

def stalkIncl (x : Y.X) : Y.X.presheaf.stalk x →ₐ[F] Y.Fn :=
  { algebraMap (Y.X.presheaf.stalk x) Y.X.functionField with
    commutes' := fun a => algebraMap_germ (U := ⊤) trivial (algX Y.str ⊤ a) }

variable {Y σ}

def base (y : Y.pts σ) : Y.X := y.1 (IsLocalRing.closedPoint ℂ)

def evStalk (y : Y.pts σ) : Y.X.presheaf.stalk (base y) →+* ℂ := (Scheme.stalkClosedPointTo y.1).hom

theorem evStalk_germ {y : Y.pts σ} {U : Y.X.Opens} (h : base y ∈ U) (a : Γ(Y.X, U)) :
    evStalk y (Y.X.presheaf.germ U _ h a) = ev Y.str σ U a y := by
  have hy : ⊤ ≤ y.1 ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y.1 h).ge
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U h)
  refine e.trans ?_
  show _ = valR y.1 U a
  rw [valR, dite_eq_left hy]
  rfl

def germIncl (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] Y.FnC σ :=
  CxExt.map σ (Y.stalkIncl (base y))

def germEv (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] ℂ :=
  CxExt.lift (evStalk y) fun a => (evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top a)

def HasVal (y : Y.pts σ) (f : Y.FnC σ) (c : ℂ) : Prop :=
  ∃ a b, germEv y b ≠ 0 ∧ germIncl y b * f = germIncl y a ∧ germEv y a = germEv y b * c

def RegC (y : Y.pts σ) (f : Y.FnC σ) : Prop := ∃ c, HasVal y f c

open Classical in
def val (y : Y.pts σ) (f : Y.FnC σ) : ℂ := if h : RegC y f then h.choose else 0

variable {y : Y.pts σ} {f f' : Y.FnC σ} {c c' : ℂ}

def regSet (f : Y.FnC σ) : Set (Y.pts σ) := {y | RegC y f}

end Var

end GlobalTheory.ProjVar
