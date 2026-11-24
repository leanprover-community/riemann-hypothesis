module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

namespace LieModel

def Extends (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G) : Prop :=
  IsTanAt G _ v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ v.left

def lat (M : LieModel G ξ E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}

def omLat (M : LieModel G ξ E) : Lat ξ (Module.Dual Ω E) := M.lat.dual

def eigLat (M : LieModel G ξ E) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) (σ : O →+* Ω) : Lat ξ E :=
  M.lat.inter (eigSp ρ σ)

variable {R : Type} [CommRing R] [IsLocalRing R]

def ValAt (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) (w : epsAt z ⟶ G) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧
      w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left

def fibAt (M : LieModel G ξ E) (L : Lat ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C]
    {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) : Submodule R EC :=
  Submodule.span R {w | ∃ (h : genPt ξ ⤳ centre z) (e : E), e ∈ L ⟨centre z, h⟩ ∧
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt w)}

end LieModel

end GlobalTheory.CompanionTheory.Ar
