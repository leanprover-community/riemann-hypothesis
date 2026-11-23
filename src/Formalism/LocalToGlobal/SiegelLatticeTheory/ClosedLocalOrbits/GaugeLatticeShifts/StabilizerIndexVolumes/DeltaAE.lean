module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

theorem deltaAE_holds (D : D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : DeltaAE D δ M := by
  intro hA
  have h := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun p hp => ?_
  intro hg
  apply hp
  have hδ : δ p ≠ 0 := (hA p).2.1
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) := (isUnit_iff_ne_zero.2 hδ).map _
  have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  have hinv : Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
    calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))
        = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) := by
          rw [mul_comm (algebraMap _ _ (δ p)), e1, mul_one]
      _ = (Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) *
            algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ := by
          rw [mul_assoc]
      _ = _ := by rw [Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hinv, (D.s.atP p).O_def]
  have hmem : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := hg.2.1.2
  have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨(δ p)⁻¹, hmem⟩ := rfl
  rw [this]
  exact isIntegral_algebraMap

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
