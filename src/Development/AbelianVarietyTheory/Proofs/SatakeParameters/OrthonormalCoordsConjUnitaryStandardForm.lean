module

public import Formalism.LocalToGlobal.HermitianForms.TiedStep
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.TopLawQ

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory

theorem unitary_conj_orthonormal : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  intro D n J crd γ hc hγ
  set σ : D.host.E →+* D.host.E := (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) with hσ
  have hg : cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * J * (γ : Matrix (Fin n) (Fin n) D.host.E) = J := hγ
  have h1 : (crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  rw [cT_mul, cT_mul]
  calc cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * cT σ (crd : Matrix (Fin n) (Fin n) D.host.E)) *
        ((crd : Matrix (Fin n) (Fin n) D.host.E) * (γ : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E))
      = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * (γ : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        simp only [Matrix.mul_assoc]
    _ = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [hc, hg, ← hc]
    _ = cT σ ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) * ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, cT_one, Matrix.one_mul]

end GlobalTheory
