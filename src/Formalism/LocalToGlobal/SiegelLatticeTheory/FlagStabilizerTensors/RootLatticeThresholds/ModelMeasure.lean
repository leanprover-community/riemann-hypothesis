module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BigCellDensity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFifth
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

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.ModelMeasure

open Formalism.MainNotions.BigCellDensity

theorem mp_modelK {r k : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1)) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {δ : Formalism.FourierDecayAlt.B.Mat k r} (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV k r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (wPt pN), ‖d (wPt pN q.1.1)‖ = ‖d (wPt pN q.1.2)‖)
    (hZ : Zhat k r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP (wPt pN) d) (μ : Measure (Mt k r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords k r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) = c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ (wPt pN) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt Ds.k_pos)
  exact Formalism.L2.SG.flagStabilizerModel.mp_model pN Ds hδ hd hdm hZ μ hconc c hmap

end Formalism.L2.SG.ModelMeasure

end
