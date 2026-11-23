module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.frame_form_coboundary_relation : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ)
    (hr : r = j + 1 + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (y : CH.Cn (Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r) j) (w : CH.Cn (gr Fil r) (j + 1)),
    (∀ s, (show sqM _ _ _ from y s).1 = Ideal.Quotient.mk _
      ((Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
        (Φ.A.map (Q.j _)).hom (E.form σ (Fin.succ ∘ I) x s))) →
    (∀ s, (show sqM _ _ _ from w s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.cons 0 (Fin.succ ∘ I)) x s)) →
    CH.d _ j y = -(CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC (j + 1) w := by
  exact @GlobalTheory.CompanionTheory.GrDelta.gr_delta
