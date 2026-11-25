module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.hasOrigin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∃ h : W.HasOrigin, push (W.origin h) u = r0 F.η F.Ψ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW
  obtain ⟨f, hf, -⟩ := hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)
  have hz : ∀ i, f (W.z i) = 0 := by
    intro i
    obtain ⟨g, a, b, -, -, hzi⟩ := hW.var i
    rw [hzi, map_sub]
    have h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b := by
      rw [← hf]
      rfl
    have h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b := by
      show f (algebraMap O R _) = _
      rw [AlgHom.commutes]
      rfl
    rw [h1, h2, sub_self]
  haveI := W.fin
  let ψ : MvPowerSeries W.σ O →ₐ[O] O := f.comp W.π
  have hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p :=
    _root_.UpperTheory.V.UnitaryThreeInertia.Tan.map_eq_cc ψ (fun i => hz i)
  have hO : W.HasOrigin := by
    intro p hp
    rw [← hψ]
    show f (W.π p) = 0
    rw [hp, map_zero]
  refine ⟨hO, ?_⟩
  have heq : W.origin hO = f := by
    ext x
    obtain ⟨p, rfl⟩ := W.surj x
    rw [UpperTheory.V.Alg.WPres.origin_π, ← hψ]
    rfl
  rw [heq, hf]
  exact MonoidHom.ext fun g => rfl
