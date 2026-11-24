module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentatives
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

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linear_forms_bounded_representatives : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ M0 : LatW D, IsPrimitiveSub M0 (L0X D Λ (lf D F0)) → ∃ reps : Finset (M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E), (reps.card : ℝ) ≤ NT D u ^ 2 ∧ ∀ ψ : M0 →ₗ[𝓞 D.host.E] 𝓞 D.host.E, ∃ ψ₀ ∈ reps, ∃ v ∈ L0X D Λ (lf D F0), ∀ x : M0, ((ψ x - ψ₀ x : 𝓞 D.host.E) : D.host.E) = (D.sp.X 0).hT v x := by
  first | exact @GlobalTheory.LoopC.FunIdx.funIdx | exact GlobalTheory.LoopC.FunIdx.funIdx | (intros; apply GlobalTheory.LoopC.FunIdx.funIdx <;> assumption)
