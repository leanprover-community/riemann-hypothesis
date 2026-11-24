module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
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

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Proper (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (Cs : Set (B.Mat k n))
    (U : Set (B.Mat k n)) : Prop :=
  ∀ y ∈ U, ∃ V ∈ 𝓝 y, ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧ ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K →
    ∀ ξ, PBG.InR B0 ξ → D.castM e (PBQ.sP Bj x) * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs

end defs

def PbWords : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) →
    IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → (∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) →
    Proper Bj B0 e Cs U →
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y

def PbLoc : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    B.CkOn ⊤ (B.GV k n) H → IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → Proper Bj B0 e Cs U →
    ∀ y ∈ U, y ∈ B.GV k n → CapelliWordSumExpansion.Loc ⊤ (PBQ.pbF Bj B0 e H) y

end Formalism.FourierDecayAlt.P.PartialBesselProperness
