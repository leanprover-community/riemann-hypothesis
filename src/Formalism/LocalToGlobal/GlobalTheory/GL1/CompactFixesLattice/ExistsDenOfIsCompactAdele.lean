module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
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

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_intAd : IsOpen ((intAd F : Subring (AF F)) : Set (AF F)) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem algebraMap_mem_intAd (m : 𝓞 F) : algebraMap F (AF F) (m : F) ∈ intAd F :=
  fun v => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.int_R v m

theorem smul_mem_intAd (m : 𝓞 F) {a : AF F} (ha : a ∈ intAd F) : (m : F) • a ∈ intAd F := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intAd m) ha

theorem exists_sub_mem_intAd (a : AF F) : ∃ u : F, a - algebraMap F (AF F) u ∈ intAd F :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele (R := 𝓞 F) (K := F) a

theorem mem_range_of_mem_intAd (u : F) (h : algebraMap F (AF F) u ∈ intAd F) :
    u ∈ (algebraMap (𝓞 F) F).range :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.mem_of_isInt (R := 𝓞 F) u h

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
