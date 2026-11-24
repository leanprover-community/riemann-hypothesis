module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.InertialTypesAlt.L.normLoc :
    UpperTheory.Gal.InertialTypesAlt.L.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw i1 i2 i3 i4 hmap η hη u
  obtain ⟨w0, hw0⟩ := w
  obtain rfl : below F w0 = v := (below_eq_iff w0 v).2 hw0
  have h2 := ideleNorm_finiteEmbedding (K := F) w0 u
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη (IdeleGroup.finiteEmbedding w0 u)
  rw [h2] at h3
  have hi : i1 = GroundTheory.Global.SemiLocal.algebraCompletion (below F w0) w0 := by
    apply Algebra.algebra_ext
    intro r
    exact (hmap r).symm
  subst hi
  exact h3
