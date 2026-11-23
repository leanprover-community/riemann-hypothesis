module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSf
public import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlP
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSfI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
variable {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C}

theorem upCharS_chartL (hL : UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : LabS E C Orb d} (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g) :
    UPCharSelfSt Y (selfOfLab ha hg o) Hc :=
  upCharS_at_chartL Pl.place_doubling_condition hL hie hd hY ha hg hr o Hc

variable (Xo c)

end UpFBr

end Formalism.L2.FormalSeriesBounds
