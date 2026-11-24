module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul, Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.LamCancel

theorem lam_cancel : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m)), w.IsGen → ∃ w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁), w₁.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  intro SA SB SC A _ _ B _ _ C _ _ MA MB MC hA hB hC m₁ m₂ m hm w₂ h₂ w hw
  subst hm
  have lA : (abelian₂ A MA).IsLB := DVR.linComb_isLB _ hA _ _
  have lB : (abelian₂ B MB).IsLB := DVR.linComb_isLB _ hB _ _
  have lC : (abelian₂ C MC).IsLB := DVR.linComb_isLB _ hC _ _
  have p₂ := (isGen_iff _).1 h₂
  have pw := (isGen_iff _).1 hw
  obtain ⟨w₁, T⟩ := Geo.Tor.exists_cancel lC w₂ w p₂ pw lB lA
  refine ⟨w₁, (isGen_iff _).2 (T.pgen_cancel lC p₂ pw), fun Z p z JA JB JC gA gB gC => ?_⟩
  have t := T Z p z (fun k => JC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left)) (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    (Set.mem_iInter.2 fun k => gC (((p ≫ m₁) ≫ m₂) ≫ (psum C (x2 C) k.down).left))
    (Set.mem_iInter.2 fun k => gB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    (Set.mem_iInter.2 fun k => gA (p ≫ (psum A (x2 A) k.down).left))
  refine Eq.trans ?_ (t.trans ((mul_comm _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · show Geo.Tor.gw w p z (fun k => JC (p ≫ (m₁ ≫ m₂) ≫ (psum C (x2 C) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₁ p z (fun k => JB (p ≫ m₁ ≫ (psum B (x2 B) k.down).left))
      (fun k => JA (p ≫ (psum A (x2 A) k.down).left))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w₂ (p ≫ m₁) z (fun k => JC ((p ≫ m₁) ≫ m₂ ≫ (psum C (x2 C) k.down).left))
      (fun k => JB ((p ≫ m₁) ≫ (psum B (x2 B) k.down).left))
    simp only [Category.assoc]

end GlobalTheory.LamCancel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\nimport Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordBundleIso_cancel_values_mul : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] [IsCommMonObj A] (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (MA : LB A.left) (MB : LB B.left) (MC : LB C.left), MA.IsLB → MB.IsLB → MC.IsLB → ∀ (m₁ : (G2 A).left ⟶ (G2 B).left) (m₂ : (G2 B).left ⟶ (G2 C).left) (m : (G2 A).left ⟶ (G2 C).left), m₁ ≫ m₂ = m → ∀ (w₂ : LB.Iso (abelian₂ B MB) ((abelian₂ C MC).pull m₂)), w₂.IsGen → ∀ (w : LB.Iso (abelian₂ A MA) ((abelian₂ C MC).pull m)), w.IsGen → ∃ w₁ : LB.Iso (abelian₂ A MA) ((abelian₂ B MB).pull m₁), w₁.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 A).left) (z : Z) JA JB JC, Good MA z JA → Good MB z JB → Good MC z JC → lamVal w p z JC JA = lamVal w₁ p z JB JA * lamVal w₂ (p ≫ m₁) z JC JB := by
  first | exact @GlobalTheory.LamCancel.lam_cancel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCancelValuesMulStatement =====
