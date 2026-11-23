module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

variable {R : Type} [CommRing R] {D D' : Type 1} [Category.{0} D] [Category.{0} D'] {Θ : PDF R D} {Θ' : PDF R D'}
  {P : ObjectProperty D} {P' : ObjectProperty D'}

def rA (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) :
    CH.Mor (CH.modF (Θ.res P.ι).A) (CH.modF (Θ.res Q.ι).A) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

def rQ (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) (c : R) :
    CH.Mor (sq (IdF.top (Θ.res P.ι).A) (IdF.span (Θ.res P.ι).A c)) (sq (IdF.top (Θ.res Q.ι).A) (IdF.span (Θ.res Q.ι).A c))
      (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem bij_of_sub {c : R} (m : QMor (Θ.res P.ι) (Θ'.res P'.ι) (IdF.span _ c)) (Q : ObjectProperty D) (Q' : ObjectProperty D')
    (hQ : Q ≤ P) (hQ' : Q' ≤ P') (hG : ∀ T : Q'.FullSubcategory, Q (m.G.obj ⟨T.obj, hQ' _ T.property⟩).obj) (j : ℕ)
    (z0 : Function.Bijective ((rA Θ hQ).pull j)) (zq : Function.Bijective ((rQ Θ' hQ' c).pull j))
    (g : Function.Bijective (((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j)) :
    Function.Bijective ((m.o (IdF.span _ c) fun _ => le_rfl).pull j) := by
  refine (Function.Bijective.of_comp_iff' zq _).1 ?_
  have e : ⇑((rQ Θ' hQ' c).pull j) ∘ ⇑((m.o (IdF.span _ c) fun _ => le_rfl).pull j) =
      ⇑(((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j) ∘ ⇑((rA Θ hQ).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (m.o (IdF.span _ c) fun _ => le_rfl) (rQ Θ' hQ' c) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (rA Θ hQ)
        ((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl) j x).1))
    rfl
  rw [e]
  exact g.comp z0

end CrystallineSemistableComparison.Pb.SubquotientResolution
