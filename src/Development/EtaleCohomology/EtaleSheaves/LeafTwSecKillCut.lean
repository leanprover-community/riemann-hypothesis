module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

def twCls {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (ζ : Prim q A) : (twF q j).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))

def LeafOfRingsLocSurj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (X : Scheme.{0}) (s : Sec (ofRings R M) X) (x : X), ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧
  ∃ t : M.obj Γ(U, ⊤), Sec.res w s = ofRings.sec M U t

def LeafOfRingsLocInj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (U : Scheme.{0}) (t : M.obj Γ(U, ⊤)), ofRings.sec M U t = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (v : V ⟶ U),
  Etale v ∧ u ∈ Set.range v ∧ (M.map (Scheme.Γ.map v.op)).hom t = 0

def LeafTwAdj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (u : U), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ Nonempty (Prim q Γ(W, ⊤))

def LeafTwGen : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (t : (twF q j).obj Γ(W, ⊤))
  (w0 : W), ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
    ((twF q j).map (Scheme.Γ.map O.ι.op)).hom t = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ)

def LeafTwFieldZ : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (K : CommRingCat.{0}), IsField K →
  ∀ (ζ : Prim q K) (c : ZMod q), ULift.up c • twCls j ζ = 0 → c = 0

def LeafTwPt : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (U : Scheme.{0}) (u : U) (t : (twF q j).obj Γ(U, ⊤))
  (V : Scheme.{0}) (g : V ⟶ U) (v : V), g v = u → ((twF q j).map (Scheme.Γ.map g.op)).hom t = 0 →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ ((twF q j).map (Scheme.Γ.map w.op)).hom t = 0

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (t : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U t) = ofRings.sec M V ((M.map (Scheme.Γ.map g.op)).hom t) := by
  have h := congrArg (fun f => f.hom t) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact h.symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res]

theorem sec_zero {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) :
    ofRings.sec M U 0 = 0 :=
  map_zero _

end LateralTheory.E.E8.TwSec
