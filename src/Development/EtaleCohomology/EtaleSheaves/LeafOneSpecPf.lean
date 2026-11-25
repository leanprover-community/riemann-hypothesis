module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction, Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf

-- ===== clump member: Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCochainEvaluationNaturalInRestriction : Prop :=
  ∀ {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U),
    ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) =
      Sec.res g (ev (R := R) α p s h U x)

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction =====

-- ===== clump member: Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf =====
-- clump-header: {"m": "Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf", "h": "module\n\npublic import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws\npublic import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneSpecPf

open LateralTheory.E.CupProductRingLaws

def LeafCochain0Ext : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (α β : Cochain ((chains R).obj E) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α 0 0 (by simp) U x = ev (R := R) β 0 0 (by simp) U x) → α = β

def LeafOneExists : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, IsOneCocycle q E α

def LeafPrimCover : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Nonempty (Prim q Γ(V, ⊤))

def LeafSecPrimLocal : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (q : ℕ) [NeZero q] (U : Scheme.{0}) (a b : Sec F U),
  IsUnit (q : Γ(U, ⊤)) → (∀ (V : Scheme.{0}) (g : V ⟶ U), Nonempty (Prim q Γ(V, ⊤)) → Sec.res g a = Sec.res g b) → a = b

end LateralTheory.E.LeafOneSpecPf
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf =====
