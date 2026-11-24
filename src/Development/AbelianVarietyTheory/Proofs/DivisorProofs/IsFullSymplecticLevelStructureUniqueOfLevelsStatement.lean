module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevels
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

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel

theorem _root_.GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
