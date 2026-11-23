module

public import Formalism.LocalToGlobal.HermitianForms.TiedTwSame
public import Formalism.LocalToGlobal.HermitianForms.TiedTwJ
public import Formalism.LocalToGlobal.HermitianColumns.TiedQCHost
public import Formalism.LocalToGlobal.HermitianForms.TiedTwLv
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

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

structure TwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTied D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJoint ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTied D Tw ch cols.forms
  lv : TwistedLevelData forms

  same : TwLvSame forms

  lvJ : TwistedJointForms ch cols.forms

end Formalism.L2.Forms

end
