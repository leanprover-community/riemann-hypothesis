module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.GalTw.Test

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem allTest : AllTest Xo c :=
  Frames.allTest_of_secBaseChange (Out.Laws.secBaseChange GlobalTheory.abelianSchemeLaws_all.1) E H Dw l Xo c

theorem galRul_one {ta : c.F ≃+* c.F} (h : Fixes c ta) : galRul (Xo := Xo) h 1 = 1 := by
  funext p y
  obtain ⟨q, φ, y₀, -, hq⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test h allTest p y)
  show (evR Xo c 1 (twPt h y)).val = (1 : Rul Xo c) p y
  rw [hq]
  simp only [Pi.one_apply, map_one]
  rfl

theorem galRul_const {ta : c.F ≃+* c.F} (h : Fixes c ta) (a : c.F) :
    galRul h (a • (1 : Rul Xo c)) = ta a • (1 : Rul Xo c) := by
  rw [galRul_smul h a 1, galRul_one h]

end GlobalTheory.GalTw.Test
