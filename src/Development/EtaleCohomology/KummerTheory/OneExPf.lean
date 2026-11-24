module

public import Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla
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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def TwRes0 : Prop := ∀ (q : ℕ) [NeZero q] {U X : Scheme.{0}} (x : U ⟶ X) (ζ₀ : Prim q Γ(X, ⊤)) (ζ : Prim q Γ(U, ⊤)),
  Sec.res x (twGen 0 ζ₀) = twGen 0 ζ

def DegreeZeroSectionExists : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom s) h).symm

theorem OneEx_of (hT : TwSec) (hR : TwRes0) (hS : DegreeZeroSectionExists) : OneEx := by
  intro q _ A _ hA hq
  obtain ⟨⟨ζ₀⟩, -⟩ := hT q A hA hq
  obtain ⟨α, hα⟩ := hS (ZMod q) (tw q 0) (Spec (CommRingCat.of A)) (twGen 0 ζ₀)
  refine ⟨_, α, rfl, ?_⟩
  intro U x ζ
  refine (hα U x).trans ((sec_res_map (resι (ZMod q) (tw q 0)) (x : U ⟶ Spec (CommRingCat.of A)) (twGen 0 ζ₀)).trans ?_)
  rw [hR q (x : U ⟶ Spec (CommRingCat.of A)) ζ₀ ζ]
  rfl

end LateralTheory.KummerTheory
