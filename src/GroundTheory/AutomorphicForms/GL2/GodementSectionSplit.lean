module

public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import GroundTheory.GlobalFields.Adele.IntegersLattice
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infChar (χ : HeckeCharacter K) : (InfiniteAdeleRing K)ˣ →* Circle :=
  χ.toIdele.comp ofInfinite

def infMod (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult

def infVec (y : Fin 2 → InfiniteAdeleRing K) : Fin 2 → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (y i)

def archSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (φ : (Fin 2 → mixedSpace K) → ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) : ℂ :=
  (infChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
    ((infMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s *
      ∫ a, φ (infVec (![0, (a : InfiniteAdeleRing K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) *
        (infChar (χ₁ * χ₂⁻¹) a : ℂ) * ((infMod a : ℝ) : ℂ) ^ (2 * s) ∂infiniteIdeleMeasure K

theorem toInfinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toInfinite K ((IdeleGroup.prodEquiv K).symm p) = p.1 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).1 = p.1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toFinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toFinite K ((IdeleGroup.prodEquiv K).symm p) = p.2 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).2 = p.2
  rw [ContinuousMulEquiv.apply_symm_apply]

end

end GroundTheory.Automorphic.GodementSection
