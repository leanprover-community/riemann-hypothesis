module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

section WDLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
variable {g : ℕ} [Fact g.Prime]

end WDLaws

section Comparison₂

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def LabTie (T : GlobalTheory.RowTie.WDTie N A) (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (γ : Fin 2 → PlE H → G H.E N.Om) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    IsTeich (τ k) ∧ TameGenAt (N.plOm.1 (A.plGw k v)) (γ k (A.plGw k v)) ∧
      ∀ a : A.LP (A.plGw k v), A.items₂ k (A.plGw k v) a = WD.lab (τ k) (γ k (A.plGw k v)) (T.e _ a)

theorem tieLab_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowCopy.TieLab N A := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim]
    exact WD.natDegree_lab_le _ _ _

end Comparison₂

section Inhabited

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end Inhabited

end GlobalTheory.LabLaws
