module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFCstmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Classical

noncomputable def _root_.Formalism.FourierDecayAlt.KB.PStdCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F → CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (waveG (p.T.bs j) s w (slv p.T F j hj w h hh.2)) (slv p.T F j hj w h' hh'.2)

end
end Formalism.FourierDecayAlt.KB

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

noncomputable def _root_.Formalism.FourierDecayAlt.P.TBBx5.CurvatureIntegralOfPartsCpt : Prop :=
  P5.ThmPActualCpt → KB.PStdCpt → KB.VIsoCpt → KB.SizeStdCpt → KB.DegWave → PBL.FormPosCpt →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → WaveGrid p nn Y Λ K N →
    TBB.KernelFourierIntegralBound p nn F Y Λ K N

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

noncomputable def _root_.Formalism.FourierDecayAlt.P.TBBx5.IntegralFourFromComponentsCpt : Prop :=
  P5.ThmPActualCpt → KB.SizeStdCpt → KB.DegLift → PBL.FormPosCpt →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ),
    KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → LiftGrid p nn Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

noncomputable def _root_.Formalism.FourierDecayAlt.P.CutBP.NFTopFormAllCpt : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
      NFTopForm p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) w

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace
noncomputable section
open Classical

end
end Formalism.FourierDecayAlt.P.CutBP
