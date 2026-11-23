module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem diffVanish_chiPic_structureModule {K : Type} [Field K] (A : AbVar K) :
    letI := A.algΓ
    DiffVanish (A.dim + 1) (chiPic K (QCoh.structureModule A.X.left)) := by
  letI := A.algΓ
  refine diffVanish_chiPic_of_isProjOver (f := A.X.hom) (fun r => rfl) _
    (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2 ?_
  refine (QCoh.suppDim_le _).trans ?_
  rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]

theorem inter_update_add {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) (a b : Pic A.X.left) :
    inter A (Function.update c i (a + b)) = inter A (Function.update c i a) + inter A (Function.update c i b) := by
  letI := A.algΓ
  exact congrFun ((diffVanish_chiPic_structureModule A).multiDiff_update_add_of_le_card hJ.ge c i a b) 0

def interAdd {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) : Pic A.X.left →+ ℤ :=
  AddMonoidHom.mk' (fun a => inter A (Function.update c i a)) (inter_update_add A hJ c i)

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  letI := A.algΓ
  exact congrFun (multiDiff_comp_equiv e c _) 0

theorem inter_multilinear_and_symm :
    ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim →
      (∃ M : (J → Pic A.X.left) →ₘₗ[ℤ] ℤ, ∀ c, M c = inter A c) ∧
      ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  refine ⟨⟨MultilinearMap.mk' (fun c => inter A c) (fun c i a b => inter_update_add A hJ c i a b)
    (fun c i n a => map_zsmul (interAdd A hJ c i) n a), fun c => rfl⟩, fun J' _ e c => inter_comp_equiv A e c⟩

end GlobalTheory.AV.AbVar
