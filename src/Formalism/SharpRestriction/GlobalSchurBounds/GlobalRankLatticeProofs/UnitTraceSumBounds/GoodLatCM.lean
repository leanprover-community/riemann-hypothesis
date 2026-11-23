module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext


variable {E : Type} [Field E] [NumberField E]


end Formalism.MainNotions.Ext


namespace Formalism.MainNotions.Ext

theorem discr_K {R : Ranks} (H : Host R) : discr H.K = -(H.d : ℤ) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hm : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx : (⟨H.sqd, hm⟩ : H.K) ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) := by
    apply Subtype.ext
    push_cast
    exact H.sqd_sq
  refine Formalism.HF.P.quadDiscr_ne_one H.K (-(H.d : ℤ)) _ hx ?_ ?_ ?_ ?_
  · have key : @IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {⟨H.sqd, hm⟩} = ⊤ := by
      apply IntermediateField.map_injective (IntermediateField.val H.K)
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
        Set.image_singleton]
      first
      | rfl
      | (simp only [IntermediateField.val_mk]; rfl)
      | simp [Formalism.HC.HostRaw.K]
    convert key
    all_goals first
      | exact Subsingleton.elim _ _
      | (apply Algebra.algebra_ext; intro r; simp [Algebra.algebraMap_eq_smul_one])
  · exact Int.squarefree_natAbs.mp (by simpa using hdp.prime.squarefree)
  · omega
  · omega

end Formalism.MainNotions.Ext
