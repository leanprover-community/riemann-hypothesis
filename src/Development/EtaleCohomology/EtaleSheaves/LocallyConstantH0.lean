module

public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LocallyConstantH0

def gam {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
  ζ.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

def IsLCMap (q : ℕ) [NeZero q] (i : ℤ)
    (m : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) →+ Sec (tw q i) (Spec (CommRingCat.of B)))) :
    Prop :=
  (∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      Sec.res (Spec.map (CommRingCat.ofHom f)) (m B ζ φ) = m C (ζ.map f) (lcMap f φ)) ∧
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (c : ZMod q), m B ζ (LocallyConstant.const _ c) = c.val • twGen i (gam ζ)

def LCMap : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ m, IsLCMap q i m

def LCBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Bijective (m B ζ)

theorem localConstant_H0 (hM : LCMap) (hB : LCBij) : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := by
  intro hA9 q _ i
  obtain ⟨m, hm⟩ := hM q i
  obtain ⟨-, e0, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨fun B _ ζ => (AddEquiv.ofBijective (m B ζ) (hB q i m hm B ζ)).trans (e0 (Spec (CommRingCat.of B))), ?_⟩
  intro B C _ _ f ζ φ
  simp only [AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  rw [hnat, hm.1]

end LateralTheory.E.LocallyConstantH0
