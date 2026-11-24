module

public import Formalism.HermitianCurvature.StatementD
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

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def SliceIntCut : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε : ℝ) (i : ℕ) (hi : i ≤ P0.r),
    1 ≤ i → 2 ≤ P0.k → B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) →
    C6.IsCut0 χ → 0 < ε → ∀ (p : C.LPt) (hp : D.IsLocPt p i), ∀ (e : Wd.Ix (Fin w.length)),
    ∀ γ ∈ B.GV P0.k (P0.r - D.ptSize p),
    Integrable (fun ξ : U.Xi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.castV (by have := hp.2; omega) T.base.z) (D.castV (by have := hp.2; omega) T.base.z') ξ •
          D.castF (by have := hp.2; omega) (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e)
            (U.gaXi P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
