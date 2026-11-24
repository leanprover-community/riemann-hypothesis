module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
