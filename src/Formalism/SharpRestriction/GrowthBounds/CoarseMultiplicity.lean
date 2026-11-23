module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio
public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem witt_identification_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) : WittIdent :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem restForm (D : Formalism.BasicNotions.D7) : RestForm :=
  restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus

theorem stmtEExt_of_rawTail1 {D : Formalism.BasicNotions.D7} (h : admitted D → RestRawTail1) : ExtendedClosedForm D :=
  stmtEExt_of fun hA => paired_lifts_of_identity (witt_identification_of_admitted hA) (h hA) (restForm D)

def RawTailReduction : Prop := RestAsmRT

theorem stmtEExt_of_15c {D : Formalism.BasicNotions.D7} (h : admitted D → RawTailReduction) : ExtendedClosedForm D :=
  stmtEExt_of_rawTail1 fun hA => restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res))) (h hA)

end Formalism.MainNotions.ColumnSystems.Pf
