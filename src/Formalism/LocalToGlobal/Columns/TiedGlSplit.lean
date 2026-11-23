module

public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)


include hc in
theorem gls_trace_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a + cO E a := by
  obtain ⟨b0, hb0⟩ := rll_norm_mem hc a
  obtain ⟨b1, hb1⟩ := rll_norm_mem hc (a + 1)
  refine ⟨b1 - b0 - 1, ?_⟩
  rw [map_sub, map_sub, map_one, hb1, hb0, map_add (cO E), map_one]
  ring

end Tr


variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)



end Formalism.L2.Col
