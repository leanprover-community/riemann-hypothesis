module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem isFrameFam_mul_infMat_inv : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsFrameFam V ε fr → ∀ b : GA D V,
        IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  intro D θ hθ V ε fr h b τ
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have h2 : infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, inv_mul_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have hu : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := IsUnit.of_mul_eq_one _ h2
  have hinv : (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ = infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ :=
    Matrix.inv_eq_right_inv h1
  refine ⟨?_, ?_⟩
  · show IsUnit (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)
    rw [hinv]
    exact (h τ).1.mul hu
  · show (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) *
        (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) = _
    rw [hinv, Matrix.conjTranspose_mul]
    have e := GlobalTheory.Doubling.infMat_isometry (V := V) hθ τ b⁻¹
    rw [← (h τ).2] at e ⊢
    simpa only [Matrix.mul_assoc] using e

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
