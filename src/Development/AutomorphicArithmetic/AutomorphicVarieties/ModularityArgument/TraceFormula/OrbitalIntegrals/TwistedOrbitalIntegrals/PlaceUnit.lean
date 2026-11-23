module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.placeUnit :
    UpperTheory.V.Z.Tf.Orb.UnitMatch → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.PlaceData → UpperTheory.V.Z.Tf.Orb.PlaceOfLocal → UpperTheory.V.Z.Tf.Orb.PlaceInt → UpperTheory.V.Z.Tf.Orb.PlaceUnit := by
  intro hM hU hD hL hI hB F E _ _ _ _ _ _ σ hσ v w hw hur n _ _ _ _ mE mF hE hF vE vF
  obtain ⟨i1, i2, i3, i4, s, hs, hr, h1, h2, h3⟩ := hD F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  haveI : CharZero (v.adicCompletion F) := algebraRat.charZero _
  obtain ⟨hH, hP⟩ := @hL F E _ _ _ _ _ _ σ hσ v w hw i1 i2 i3 i4 s hs hr h1 h2 n _ _ _ _ mE mF hE hF _ _
  have hc : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hm := @hM hB _ _ _ _ _ _ _ _ _ _ _ i1 i2 i3 i4 (h3 hur) s hs n _ _ _ _ _ mF hH hF
    (by rw [Measure.map_apply hc.measurable (hU _ n).1.measurableSet, ← hI.2 F E v w hw n, vE])
    (by rw [hI.1 F v n, vF])
  have := hP _ (hU _ n).2.2 _ (hU _ n).2.2 hm
  rw [hI.2 F E v w hw n, ← hI.1 F v n]
  exact this
