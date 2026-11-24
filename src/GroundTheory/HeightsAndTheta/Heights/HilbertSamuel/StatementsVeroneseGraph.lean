module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace Veronese

def forms (D : ℕ) : Ix (Idx D) → MRing (GlobalTheory (Fin (D + 1))) :=
  fun q => X ⟨(), q.2.1.1⟩ * X ⟨(), q.2.1.2⟩

end Veronese

def VeroneseGraphImage.Statement : Prop :=
  ∀ D : ℕ, imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)))
      (graphIdeal ⊥ (Veronese.forms D)) = coordIdeal ℤ (Veronese.x D)

def VeroneseGraphDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (graphIdeal ⊥ (Veronese.forms D)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
