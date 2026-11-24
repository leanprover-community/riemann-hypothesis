module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
