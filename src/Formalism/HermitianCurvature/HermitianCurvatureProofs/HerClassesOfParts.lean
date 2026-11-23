module

public import Formalism.HermitianCurvature.StatementQ
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Struct

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem inK_act_span {G G' : Set V} (M : SlopeTestRemainingChoices S (Pr V)) (hM : ∀ a b, ∀ Φ ∈ G, (M a b).1 Φ ∈ Submodule.span ℂ G')
    (x : Ix S → V) (hx : ∀ a, x a ∈ Submodule.span ℂ G) : ∀ a, ∑ b, (M a b).1 (x b) ∈ Submodule.span ℂ G' := by
  intro a
  refine Submodule.sum_mem _ (fun b _ => ?_)
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ G').comap (M a b).1 :=
    Submodule.span_le.mpr (fun Φ hΦ => hM a b Φ hΦ)
  exact hle (hx b)

end Struct

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

end Classes

end Formalism.FourierDecayAlt.P5
