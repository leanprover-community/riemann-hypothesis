module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFrames

theorem smor_Fr_frame : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) {V V' : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d) (c' : Chart γ' p q κ' V' d) (hc : c.Good) (hc' : c'.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D)
    (hQ' : ∀ T, Q' T → InU V' T) (hD' : Q' c'.D) (e : c.D ⟶ (m.mor p).functor.obj c'.D),
    (∀ i, e.φ (c.t i) = c'.t i) →
      SMor.Fr (m.smor Q Q' h) (c.frame hc Q hQ hD) (c'.frame hc' Q' hQ' hD') (ObjectProperty.homMk e) := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m V V' d c c' hc hc' Q Q' h hQ hD hQ' hD' e he i T s s'
  change (s'.hom.φ (e.φ (c.t i)) - s.hom.φ (e.φ (c.t i)) : T.obj.B) = s'.hom.φ (c'.t i) - s.hom.φ (c'.t i)
  rw [he]

end GlobalTheory.CompanionTheory.ChartFrames
