module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback, Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal\nimport Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel\nimport Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem sharpOver_unique : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u →
    GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' →
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  intro g n F W T T' P P' u u' h hu hS hS'
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀

  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  refine ⟨α, ⟨hpb, hmul⟩, ?_⟩
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ ε
  have l2 : (LB.LinComb (c'.P.pull κ₂) q ε).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q ε
  have l3 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' ε).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' ε).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    LBIso.chartPull (chartPullOut c'.P q' ε α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb (c'.P.pull κ₂) q ε) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q ε) (LB.LinComb c.P q ε) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q ε
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q ε) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  exact LBIso.trans P.isLB l3 h1 hbun chain.symm

end GlobalTheory.Poinc
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullback\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe\nimport Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sharp_polarization_unique_pullback : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u → GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' → ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  first | exact @GlobalTheory.Poinc.sharpOver_unique
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationUniquePullbackStatement =====
