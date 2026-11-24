module

public import Formalism.PieriBlockIdeals.StatementLP
public import Formalism.PieriBlockIdeals.PieriColumnMinors.GeneratedHighestWeightHolds
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightDominantHolds
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightSuccessive
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LpcDpartCommEps
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

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem tower_pieri : TowerPieri := TowerPieri_of completeReducibility_holds highestWeightDominant_holds

theorem pieri_rule : Pieri := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF h0 n
  have hT := tensor_tower K P M q EM B n hF
  have hb := tensor_base_case K P M q EM n (fun b => (lam2 b : K)) h0
  have hTP := tower_pieri K (Tens (Fin q) P M n) q n (fun j => Dpart K EM j) (epsY K n)
    (tensForm n B) lam2 hT hb
  apply eq_top_iff.mpr
  rw [← hTP, Submodule.span_le]
  rintro z ⟨tau, κ, ρ, hp, hcas⟩
  exact Submodule.mem_iSup_of_mem tau (Submodule.subset_span ⟨κ, ρ, hp, fun j hj => hcas j hj⟩)

theorem pieri_generated : PieriGenerated := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF hgen n
  exact pieri_rule K P M q EM B lam2 hF (generatedHighestWeight_holds K M q EM B hF _ hgen) n

end Formalism.CohomologicalDescent.LP
