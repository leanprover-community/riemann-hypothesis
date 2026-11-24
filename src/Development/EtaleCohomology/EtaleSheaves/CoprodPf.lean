module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
