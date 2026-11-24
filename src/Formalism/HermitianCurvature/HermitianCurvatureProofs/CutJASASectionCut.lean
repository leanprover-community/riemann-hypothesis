module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
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

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SARadSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
      ∀ U : M.Ty P → MA.SmQ P.r P.TT, ∃ Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ q : MA.Qp P.r P.TT,
        Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
          (((Real.sqrt (MA.wq P.k q.1 P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, (U ρ : MA.Qp P.r P.TT → ℂ) q • e ρ q.1.2

def SADescend : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ Φ ∈ Q.RadSp k r z z' π π',
      ∃ D₀ : Set (Q.Mx k r), Q.IsDom k r z z' 0 D₀ ∧ ∃ K ∈ Q.FFl k r z z' π π' 0 D₀,
        ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g →
          Q.wCell k r (Fin.last r) c * g ∈ D₀ ∧ K (Q.wCell k r (Fin.last r) c * g) = Φ c g

def SACover : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z', ∃ n ∈ Q.Nlev k r 0, ∃ n' ∈ Q.Nlev k r 0, ∃ c ∈ OmX r,
      ∃ g₁ ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g₁ ∧ g = n * (Q.wCell k r (Fin.last r) c * g₁) * n'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
