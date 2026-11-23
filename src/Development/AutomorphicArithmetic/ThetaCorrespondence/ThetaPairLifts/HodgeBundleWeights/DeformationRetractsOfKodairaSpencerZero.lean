module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
variable {C : Over (Sp (DualNumber R))} [GrpObj C] {φ : C.left ⟶ A.left} {j : A.left ⟶ C.left}
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
theorem exists_retraction_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
      ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left)
        (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i),
        IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
        (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) →
        ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  intro Pr GD E _ _ _ H Dw l Xo c K _ _ y x' _ _ A _ A' _ π π' i h _ hπ' _ hKS
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  exact GlobalTheory.DeRham.exists_retraction_of_isKSValue_one Pr.p5 GD h hA' gA' hKS
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) → ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  first | exact @_root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | exact _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | (intros; apply _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero <;> assumption)
end
