module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open IsDedekindDomain
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchSmooth

open AutomorphicForm

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cMap : mixedEmbedding.mixedSpace E →ₗ[ℝ] Cinf E where
  toFun z := fun w => z.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cMap_ringEquiv (x : InfiniteAdeleRing E) :
    cMap E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) = (infEq E).symm x := by
  funext w
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E x).2 ⟨w, IsTotallyComplex.isComplex w⟩ = _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

def mMap : ArchMatrix E a →ₗ[ℝ] Lie E a where
  toFun x := fun i j => cMap E ((x : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) i j)
  map_add' x y := by
    funext i j
    exact map_add (cMap E) _ _
  map_smul' c x := by
    funext i j
    exact map_smul (cMap E) c _

def toGL (u : archGroup E a) : GL (Fin a) (Cinf E) :=
  Matrix.GeneralLinearGroup.map (infEq E).symm.toRingHom ((archEquiv E a).symm u)

theorem toL_toGL (u : archGroup E a) :
    toL (toGL E a u).val = mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
  obtain ⟨b, rfl⟩ := (archEquiv E a).surjective u
  funext i j
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  exact (cMap_ringEquiv E (b i j)).symm

theorem infEmb_eq (u : archGroup E a) : infEmb E a u = infGL E a (toGL E a u) := by
  apply ga_ext
  · rw [pInf_infGL]
    ext i j : 2
    have h := congrArg (fun p => (p.1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) (prodEquiv_infEmb u)
    exact congrArg (infEq E).symm h
  · rw [pFin_infGL]
    ext i j : 2
    exact congrArg (fun p => (p.2 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i j) (prodEquiv_infEmb u)

theorem archSlice_eq (φ : GA E a → ℂ) (g : GA E a) (u : archGroup E a) :
    archSlice φ g u = chart φ g (mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
  rw [← toL_toGL, chart_val, archSlice_apply, infEmb_eq]

theorem sm_mem_archSmooth (φ : Sm E a) : φ.1 ∈ AutomorphicForm.archSmooth E a := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g'
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  let c : ArchMatrix E a := ((g' : (ArchMatrix E a)ˣ) : ArchMatrix E a)
  let F : archLie E a → ArchMatrix E a := fun Y => c * NormedSpace.exp (Y : ArchMatrix E a)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix E a)).comp (archLie E a).subtypeL.contDiff)
  have hs : ContDiff ℝ ∞ fun Y => L (F Y) := L.contDiff.comp hF
  have hmem : ∀ Y, L (F Y) ∈ invSet E a := fun Y => by
    have : L (F Y) = toL (toGL E a (g' * (isExpLieAlgebra E a).expG Y)).val := (toL_toGL E a (g' * (isExpLieAlgebra E a).expG Y)).symm
    rw [this]
    exact val_mem_invSet _
  have hc := (φ.2 g).comp_contDiff hs hmem
  have e : (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y)) =
      chart φ.1 g ∘ fun Y => L (F Y) :=
    funext fun Y => archSlice_eq E a φ.1 g _
  change ContDiff ℝ ∞ (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y))
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.ArchSmooth
