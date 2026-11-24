module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMap
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

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_finiteEtale_goodCover_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  first | exact @GlobalTheory.CoverGood.exists_good_cover | exact GlobalTheory.CoverGood.exists_good_cover | (intros; apply GlobalTheory.CoverGood.exists_good_cover <;> assumption)
