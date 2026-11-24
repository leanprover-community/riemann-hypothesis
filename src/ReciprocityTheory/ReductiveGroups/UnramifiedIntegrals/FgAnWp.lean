module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
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
import Mathlib.Topology.Sheaves.Init
import Formalism.TorsionNormIteration.InvIntegralOfClass

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem shortW_map (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ) (ι : ℂ ≃+* ℂ_[l]) :
    A.shortW (ι g2) (ι g3) = (A.shortW g2 g3).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wp_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) :
    A.wpReg (A.shortW (ι L.g₂) (ι L.g₃)) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curveBridge (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)).2.2.1
  rw [← h1, h2, shortW_map]

end ReciprocityTheory.ChartRestriction.L1
