module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersectiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
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

namespace GlobalTheory.AV.AmpleTopPos

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  unfold inter
  rw [GlobalTheory.multiDiff_comp_equiv]

theorem inter_top_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  intro K _ A c hc J _ hJ
  obtain ⟨L, hL, hr, rfl⟩ := hc
  have hA : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hr, rfl⟩
  have e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have h1 : inter A (fun _ : J => cls L hL) = inter A (fun _ : Fin A.dim => cls L hL) :=
    (inter_comp_equiv A e (fun _ : J => cls L hL)).symm
  rw [h1, GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin A.dim) (fun _ => L) (fun _ => hL)]
  letI := A.algΓ
  obtain ⟨hI, -, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  have hp' : IsProjOver (strHom K (X := A.X.left)) := by rw [hs]; exact hp
  exact GlobalTheory.CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K A.X.left hp' A.dim
    (GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A) L hA

end GlobalTheory.AV.AmpleTopPos
