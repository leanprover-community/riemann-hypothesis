module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsMM
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def ConjExt : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ lam : Qbar →+* ℂ_[p], ∃ σ : ℂ_[p] →+* ℂ_[p], IsConjP D lam σ

def FrameONB : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
        (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
      ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) →
      Formalism.L2.Th1.H.relIdx
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
        (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ →
    ∀ (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p]),
      Formalism.L2.Th1.Top.IsFrameH σ ι g₁ γ B' →
    ∀ σp : ℂ_[p] →+* ℂ_[p], IsConjP D lam σp →
      IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σp
        (fun i k => B' k.1 ((Fintype.equivFin D.what₂.Tau).symm i))

end Formalism.L2.KerInert
