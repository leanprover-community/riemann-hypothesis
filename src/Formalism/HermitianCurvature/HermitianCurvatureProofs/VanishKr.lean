module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vanish_kr (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    {H : B.Mat k n → (Wq →L[ℂ] Wp)} {Cs : Set (B.Mat k n)} (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0)
    {U : Set (B.Mat k n)} (hP : Proper Bj B0 e Cs U) : VanishL Bj e (PBG.Kr B0 H) U := by
  intro y hy
  obtain ⟨V, hV, K, hK, hVK⟩ := hP y hy
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, K, hK, fun g hg hgG x hx hxK => ?_⟩
  rw [Formalism.FourierDecayAlt.P.PBG.kr_eq]
  rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.PBG.ae_inR B0] with ξ hξ
  rw [Formalism.FourierDecayAlt.P.PBG.rho_pR]
  have hG : sE Bj e x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k n :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (sE_GV Bj e x) hgG) hξ.2.1) hξ.1.1
  have hC := hVK g (interior_subset hg) hgG x hx hxK ξ hξ
  rw [hH _ hG hC]
  simp

end Formalism.FourierDecayAlt.P.PartialBesselProperness
