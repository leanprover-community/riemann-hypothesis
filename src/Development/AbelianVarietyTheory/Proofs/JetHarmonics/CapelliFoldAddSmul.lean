module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem capelliFold_good {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) :
    ∀ w : List (Bool × ℝ), Formalism.FourierDecayAlt.P.Qx2.Good k r 0 Set.univ
      (fun f : B.Mat k r → E => List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) f w)
  | [] => Formalism.FourierDecayAlt.P.Qx2.good_id
  | a :: w => (Formalism.FourierDecayAlt.P.Dx1.LZ.good_Tc (k := k) (r := r) (E := E) s (a.2 : ℂ)).comp (capelliFold_good s w)

theorem capelliFold_add_smul :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ))
      (a : ℂ) (X Z : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) Z →
      ∀ g ∈ B.GV k r,
        (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • Z) w) g =
          (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) g +
            a • (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (Z) w) g := by
  intro k r Wp Wq _ _ _ _ _ _ s w a X Z hX hZ g hg
  exact (capelliFold_good s w).lin X Z a (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hX)
    (Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck hZ) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)

end GlobalTheory
