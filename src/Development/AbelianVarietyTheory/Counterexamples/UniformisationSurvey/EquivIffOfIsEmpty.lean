module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairTest

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem ext_val {T : Over (Spec (CommRingCat.of R))} {g g' : GtPt D T} (hb : g.b = g'.b)
    (hs : ∀ χ y J, Geo.Tor.Good D.P.L y J → Geo.Tor.val (g.s χ) (𝟙 _) y J = Geo.Tor.val (g'.s χ) (𝟙 _) y J) :
    g = g' := by
  obtain ⟨b, s, h, _, _⟩ := g
  obtain ⟨b', s', h', _, _⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ =>
    GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ) (Geo.Tor.corr_of_val D.P.isLB (hs χ))
  rfl

theorem isPull_unique {T T' : Over (Spec (CommRingCat.of R))} {h : T'.left ⟶ T.left} {g : GtPt D T}
    {a a' : GtPt D T'} (H : GtPt.IsPull h g a) (H' : GtPt.IsPull h g a') : a = a' :=
  ext_val (Over.OverMorphism.ext (H.1.trans H'.1.symm)) fun χ _ _ hJ =>
    (Geo.Tor.val_corr hJ (H.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (H'.2 χ) (𝟙 _)).symm

section Empty

variable {T : Over (Spec (CommRingCat.of R))} [IsEmpty T.left]

end Empty

variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]

end GlobalTheory.TorsionPairTest
