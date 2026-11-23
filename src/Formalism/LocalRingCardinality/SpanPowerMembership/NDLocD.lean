module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem continuous_rHom : Continuous (rHom (E := E) hj) :=
  by apply _root_.UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom <;> assumption

instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact

def eDec : ↥(Dec (F := E) A) ≃* ↥(KwF (E := E) j).fixingSubgroup :=
  (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).symm

theorem eDec_comm (g : ↥(Dec (F := E) A)) (x : Ω) :
    ((eDec hj g : ↥(KwF (E := E) j).fixingSubgroup) : GQ l) (j x) = j ((g : G E Ω) x) := by
  rw [← j_rHom hj]
  congr 2
  exact congrArg Subtype.val ((MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).apply_symm_apply g)

theorem continuous_eDec_symm : Continuous (eDec (E := E) hj).symm := continuous_rHom hj

theorem continuous_eDec : Continuous (eDec (E := E) hj) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).toEquiv)
    (continuous_rHom hj)

end Formalism.BasicNotions.Examples₂.LB

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

end Formalism.BasicNotions.Examples₂
