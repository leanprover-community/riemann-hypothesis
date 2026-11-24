module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def CechDSq.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R] (G : Cell U → Type v)
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J),
    (∀ (I J K : Cell U) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1),
      (ρ J K hJK).comp (ρ I J hIJ) = ρ I K (hIJ.trans hJK)) →
    ∀ (i : ℕ) (s : Cech.Cochain G i), Cech.d G ρ (i + 1) (Cech.d G ρ i s) = 0

section Hypotheses

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem locResS_comp (I J K : StdCell N) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (locResS (S := S) (M := M) J K hJK).comp (locResS I J hIJ) = locResS I K (hIJ.trans hJK) := by
  refine LinearMap.ext fun x => ?_
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locRes hJK (locRes hIJ _) = locRes (hIJ.trans hJK) _
    rw [locRes_mk, locRes_mk, locRes_mk]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
