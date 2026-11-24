module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSympLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullSymplecticLevelStructureOfTateIso
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

theorem _root_.GlobalTheory.T.exists_fullSymplecticLevelStructure_of_tateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  first | exact @GlobalTheory.FullLevel.exists_sympLevel_of_tate | exact GlobalTheory.FullLevel.exists_sympLevel_of_tate | (intros; apply GlobalTheory.FullLevel.exists_sympLevel_of_tate <;> assumption)
