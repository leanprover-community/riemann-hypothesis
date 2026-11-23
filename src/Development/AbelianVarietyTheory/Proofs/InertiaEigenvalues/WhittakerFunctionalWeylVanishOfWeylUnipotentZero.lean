module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem wS_nS_wS_eq_unit {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by
  have h1 : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := z.mul_inv
  have cw : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have cn : ∀ t : k, ((nS t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
    fun _ => rfl
  have cm : ∀ s : kˣ, ((mS s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] := fun _ => rfl
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, cw, cn, cm]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two] <;> ring_nf <;> simp [h1]

theorem lam_flip_eq_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ μK hμ Ψ hΨ h0 a c
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ z ∂μK, IsUnit z := ae_iff.2 hnull
  unfold Et.abelian₂
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [hae] with z hz
  obtain ⟨u, rfl⟩ := hz
  simp only [Pi.zero_apply]
  rw [wS_nS_wS_eq_unit u, hΨ.2, h0, mul_zero, zero_mul]

end GlobalTheory.JR
