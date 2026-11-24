module

public import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.norm_algebraMap_base_le_one_of_placesOver :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w w' : PlacesOver E q) (a : F),
        ‖algebraMap E (w.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 → ‖algebraMap E (w'.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 := by
  intro F E _ _ _ _ _ q w w' a
  have key : ∀ u : PlacesOver E q,
      ‖algebraMap E (u.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 ↔
        Valued.v (algebraMap F (q.adicCompletion F) a) ≤ 1 := by
    intro u
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsScalarTower.algebraMap_apply F E (u.1.adicCompletion E),
      ← completionMap_algebraMap q u.1, valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) u.1.asIdeal).ne'
  exact fun h => (key w').2 ((key w).1 h)
