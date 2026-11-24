module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Mathlib.Order.Int.LeastGreatest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LiftOUnique\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

theorem chart_of_point {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y I, Good L y I → sval s (𝟙 Y) y I = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y I) :
    ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j := by
  intro j
  refine fn_ext fun y hy0 => ?_
  have hy : y ∈ LB.wchart L φ j := hy0
  choose I hI using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
  have hIy : Good L y I := hI
  have mm := hIy.mem φ (𝟙 _)
  have T0 := sec_trans s (𝟙 _) y hy mm
  set τ := (trF φ ε (𝟙 _) y j (fun k => I (𝟙 _ ≫ φ k))).val with hτ
  have RHS : gs (𝟙 _) y (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) *
      (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
      τ * ∑ i, gs (𝟙 _) y ⊤ (b i) * sval (t i) (𝟙 _) y I := by
    rw [gs_sum _ y _ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy, gs_res _ y le_top hy, sec_trans (t i) (𝟙 _) y hy mm, hτ]
    exact mul_left_comm _ _ _
  exact T0.trans ((congrArg (fun x => τ * x) (h y I hIy)).trans RHS.symm)

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem hformF (k : ℕ) (ρ : D.toPre.X) :
    FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F ρ) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem hformF' (k : ℕ) (ρ : D.toPre.X) :
    FormEq (DegPre.famφ D.toPre F ρ) (DegPre.famε k)
      (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem coordsF {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J) :
    (∀ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)), ∃ c : Fin m → F,
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J) ∧
    (∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0) := by
  have hL := D.toPre.P.isLB
  have eT : Over.mk (Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V)))) = TF (R := V) F := by
    rw [← TF_hom]; rfl
  have hbF' := hb F (algVF (F := F) (V := V))
  rw [eT] at hbF'
  let b' := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TF (R := V) F) D.toPre.P.A).left
  have hB := hbF' b' (fun i j => rfl)
  have hb' : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (b' i) (𝟙 _) y J = sval (bF i) (𝟙 _) y J := fun i y J hJ => by
    rw [hbF i y J hJ]
    exact (sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp])
  refine ⟨fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨t', ht'⟩ := exists_sec hL (hformF' k ρ) t
    obtain ⟨r, hr, -⟩ := hB t'
    choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (r i)
    refine ⟨c, fun y J hJ => ?_⟩
    rw [← ht' _ (𝟙 _) y J hJ, sval_lin (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom (r i)) b' hr (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb' i y J hJ, gF, RingHom.comp_apply, ← hc i]
  · let z0 : LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (TF (R := V) F) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
      (DegPre.famε k)) := SecOps.secZero
    have r1 := chart_of_point hL z0 (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b' (fun y I hI => by
        rw [sval_zero_of (fun j => rfl) _ y I (hI.mem _ _), ← hc y I hI]
        exact Finset.sum_congr rfl fun i _ => by rw [hb' i y I hI]; rfl)
    have r0 : ∀ j, z0.f j = ∑ i, resTop _ ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom 0) * (b' i).f j := fun j => by
      simp only [map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]; rfl
    obtain ⟨r, -, hu⟩ := hB z0
    have e := (hu _ r1).trans (hu _ r0).symm
    funext i
    have hi : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i) = 0 := congrFun e i
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hi
    simpa using this

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

def RepF {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))) (c : Fin m → F) : Prop :=
  ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
    sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J

theorem coordsO {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (σ : D.toPre.SecB k ρ) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hσF : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval σF (𝟙 _) y J = sval σ (DegPre.prB D.toPre F).left y J) :
    ∃ c : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ RepF bF σF c := by
  let bO := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TO hϖ hv) D.toPre.P.A).left
  have hBO := hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ
    (snd (TO hϖ hv) D.toPre.P.A).left)
  refine ⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩
  have e := sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd] at e
  rw [hσF y J hJ, e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have g := gs_jO hϖ hv (D := D) (𝟙 _) y (r i)
  rw [Category.id_comp] at g
  rw [g, hbF i y J hJ]
  show _ * sval (pullSec _ _ _ (b i) _) _ y J = _
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd]

theorem repF_unique {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    {bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))}
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c c' : Fin m → F}
    (h : RepF bF t c) (h' : RepF bF t c') : c = c' := by
  have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)),
      gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b :=
    fun y a b => gs_sub _ y ⊤ (by first | trivial) a b
  have h0 := hU (c - c') (fun y J hy => by
    have e1 := h y J hy
    have e2 := h' y J hy
    simp only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem fam_sum_f {k : ℕ} {Ix : Type} [Fintype Ix] (c : Ix → F) (s : Ix → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i, c i • s i).s α).f j = ∑ i, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
  classical
  have key : ∀ t : Finset Ix, ((∑ i ∈ t, c i • s i).s α).f j =
      ∑ i ∈ t, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_f, smul_f, ih]
  exact key Finset.univ

theorem fam_eq_zero (hG : GlobalFnsSt) {k : ℕ} (P : D.toPre.X → Prop) (hP : ∀ χ, ∃ α mu, P α ∧ α + k • mu = χ)
    (s : Fam D.toPre F k) (h0 : ∀ α, P α → ∀ j, (s.s α).f j = 0) : s = 0 := by
  have hL := D.toPre.P.isLB
  refine DVR.fam_ext fun χ j => ?_
  obtain ⟨α, mu, hα, rfl⟩ := hP χ
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG k mu α
  have hrel := s.fe mu α u hu hc
  refine sec_ext_val hL (s' := (0 : Fam D.toPre F k).s (α + k • mu)) (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, sval_zero_of (h0 α hα) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul, sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)]

theorem vge_coords {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c : Fin m → F}
    (hc : RepF bF t c) {r : ℚ} (ht : VGe D F v k ρ t r) : ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := ht
  have hσ : ∀ l, ∃ c' : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c' i)) ∧ RepF bF (σF l) c' := fun l =>
    coordsO hϖ hv b hb bF hbF (σ l) (σF l) fun y J hJ => by
      rw [← secScal_sval (hscal l) (𝟙 _) y hJ, Category.id_comp]
  choose c' hc'v hc' using hσ
  have hrep : RepF bF t (fun i => ∑ l, a l * c' l i) := fun y J hJ => by
    rw [sval_lin (fun l => gF D.toPre F (a l)) σF (fun j => hsum j) (𝟙 _) y hJ]

    simp only [map_sum, map_mul, gs_sum _ y ⊤ trivial, gs_mul _ y ⊤ trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc' l y J hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e := repF_unique hU hc hrep
  intro i
  rw [e]
  refine AddValuation.map_le_sum v fun l _ => ?_
  rw [AddValuation.map_mul]
  calc ((r : ℚ) : WithTop ℚ) = (r : WithTop ℚ) + 0 := (add_zero _).symm
    _ ≤ v (a l) + v (c' l i) := add_le_add (hva l) (hc'v l i)

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Rat\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Mathlib.Order.Int.LeastGreatest\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc\n\n"}
section -- clump:auto
@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing QForm

def RepsXSt : Prop := ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ), 1 ≤ k →
    ∃ rep : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ χ : X, ∃ a mu, rep a + k • mu = χ) ∧
      (∀ a a' (mu mu' : X), rep a + k • mu = rep a' + k • mu' → a = a') ∧
      (∀ x y : X, k • x = k • y → x = y)

def CeilSt : Prop := ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (π : F), v π = 1 →
    (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) →
    ∀ q : ℚ, ∃ l : F, l ≠ 0 ∧ ∀ x : F, (((q : ℚ) : WithTop ℚ) ≤ v x ↔ v l ≤ v x)

theorem uu_of (hG : GlobalFnsSt) (hT : TwistBaseChangeStatement) (hR : RepsXSt) (hC : CeilSt) : UUStatement := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv hF k hk
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨rep, hcov, hdis, hinj⟩ := hR D.toPre.X k hk
  have hπ : v (algVF (F := F) ϖ) = 1 := by
    have e := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    simpa [algVF] using e
  choose lam hlam0 hlam using fun a => hC F v (algVF ϖ) hπ hF ((Q (rep a) : ℚ) / k)
  have exb : ∀ a, ∃ b : Fin (k ^ D.toPre.P.g) → D.toPre.SecB k (rep a),
      ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin (k ^ D.toPre.P.g) → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre (rep a) i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre (rep a)) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b' := fun a => by
    obtain ⟨m, b, hm, hb⟩ := hT V D.toPre k hk (rep a)
    subst hm
    exact ⟨b, hb⟩
  choose b hb using exb
  have exF : ∀ a i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F (rep a)) (DegPre.famε k)),
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = sval (b a i) (DegPre.prB D.toPre F).left y J := fun a i => by
    obtain ⟨t, ht⟩ := exists_sec hL (hformF k (rep a))
      (pullSec D.toPre.P.L (DegPre.famφB D.toPre (rep a)) (DegPre.famε k) (b a i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun y J hJ => (ht _ (𝟙 _) y J hJ).trans ((sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp]))⟩
  choose bF hbF using exF
  have hEU := fun a => coordsF (b a) (hb a) (bF a) (hbF a)
  have hcls : ∀ a (x y : D.toPre.X), rep a + k • x = rep a + k • y → x = y := fun a x y e => hinj x y (add_left_cancel e)
  choose Fm hFm0 hFm1 using fun (p : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) =>
    exists_fam_rep (D := D.toPre) (F := F) hG D.tau_bimult k (rep p.1) (hcls p.1) (bF p.1 p.2)
  have hoff : ∀ (p : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) a₀, p.1 ≠ a₀ → ∀ j,
      ((Fm p).s (rep a₀)).f j = 0 := fun p a₀ hne =>
    hFm1 p _ (fun mu e => hne (hdis p.1 a₀ mu 0 (by rw [e, smul_zero, add_zero])))
  have comp : ∀ (c : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g) → F) a₀ j,
      ((∑ p, c p • (lam p.1 • Fm p)).s (rep a₀)).f j =
        ∑ i, resTop _ (gF D.toPre F (c (a₀, i) * lam a₀)) * (bF a₀ i).f j := by
    intro c a₀ j
    rw [fam_sum_f, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a₀ (fun a _ hne => Finset.sum_eq_zero fun i _ => by
      rw [DVR.smul_f, hoff (a, i) a₀ hne j, MulZeroClass.mul_zero, MulZeroClass.mul_zero]) (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 := hFm0 (a₀, i)
    dsimp only at h0
    rw [DVR.smul_f, h0, map_mul, resTop, resTop, resTop, map_mul, _root_.mul_assoc]
  have hcard : Fintype.card ((Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) = k ^ (D.toPre.rank + D.toPre.P.g) := by
    simp [Fintype.card_prod, pow_add]
  let e := Fintype.equivFinOfCardEq hcard
  let S : Finset D.toPre.X := Finset.univ.image rep
  have hS : ∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0 := fun χ => by
    obtain ⟨a, mu, h⟩ := hcov χ
    exact ⟨rep a, Finset.mem_image_of_mem _ (Finset.mem_univ _), mu, h.symm⟩
  have hre : ∀ (c : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → F),
      ∑ t, c t • (lam (e.symm t).1 • Fm (e.symm t)) = ∑ p, c (e p) • (lam p.1 • Fm p) := fun c => by
    rw [← Equiv.sum_comp e.symm (fun p => c (e p) • (lam p.1 • Fm p))]
    simp only [Equiv.apply_symm_apply]
  have hql : ∀ a, ((((Q (rep a) : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v (lam a) := fun a => ((hlam a (lam a)).2 le_rfl)
  refine ⟨fun t => lam (e.symm t).1 • Fm (e.symm t), ?_, fun t => ?_, fun s => ⟨fun hs => ?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg t
    rw [hre] at hg
    set p := e.symm t with hp
    have h0 : ∀ j, ((0 : Fam D.toPre F k).s (rep p.1)).f j =
        ∑ i, resTop _ (gF D.toPre F (g (e (p.1, i)) * lam p.1)) * (bF p.1 i).f j := fun j => by
      rw [← comp (fun q => g (e q)) p.1 j, hg]
    have hz := (hEU p.1).2 (fun i => g (e (p.1, i)) * lam p.1) fun y J hJ => by
      have e0 := sval_lin (fun i => gF D.toPre F (g (e (p.1, i)) * lam p.1)) (bF p.1) h0 (𝟙 _) y hJ
      rw [← e0]
      exact sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)
    have := congrFun hz p.2
    simp only [Pi.zero_apply, mul_eq_zero, hlam0, or_false] at this
    rwa [show (p.1, p.2) = p from rfl, hp, Equiv.apply_symm_apply] at this
  · refine (n1a V ϖ hϖ D Q hQ F v hv k hk S hS _ 0).2 fun α hα => ?_
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hα
    rw [zero_add]
    by_cases h : (e.symm t).1 = a₀
    · subst h
      refine ⟨1, fun _ => lam (e.symm t).1, fun _ => b _ (e.symm t).2, fun _ => bF _ (e.symm t).2,
        fun _ => secScal_of_sval hL fun y J hJ => ?_, fun _ => hql _, fun j => ?_⟩
      · rw [Category.id_comp]; exact (hbF _ _ y J hJ).symm
      · rw [Fin.sum_univ_one, DVR.smul_f, hFm0]; rfl
    · exact vge_of_zero (fun j => by rw [DVR.smul_f, hoff _ a₀ h j, MulZeroClass.mul_zero]) _
  · have hs' := (n1a V ϖ hϖ D Q hQ F v hv k hk S hS s 0).1 hs
    choose c hc using fun a => (hEU a).1 (s.s (rep a))
    have hcv : ∀ a i, ((((Q (rep a) : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v (c a i) := fun a =>
      vge_coords hϖ hv (b a) (hb a) (bF a) (hbF a) (hEU a).2 (hc a)
        (by simpa using hs' (rep a) (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    refine ⟨fun t => c (e.symm t).1 (e.symm t).2 / lam (e.symm t).1, fun t => ?_, ?_⟩
    · obtain ⟨ql, hql'⟩ := wt_coe_of_ne (v := v) (hlam0 (e.symm t).1)
      show (0 : WithTop ℚ) ≤ v (c (e.symm t).1 (e.symm t).2 / lam (e.symm t).1)
      rw [div_eq_mul_inv, AddValuation.map_mul, v_inv_coe (v := v) (hlam0 _) hql']
      have hle := (hlam (e.symm t).1 (c (e.symm t).1 (e.symm t).2)).1 (hcv _ _)
      rw [hql'] at hle
      induction h : v (c (e.symm t).1 (e.symm t).2) using WithTop.recTopCoe with
      | top => simp
      | coe qc =>
        rw [h] at hle
        have : ql ≤ qc := by exact_mod_cast hle
        exact_mod_cast (show (0 : ℚ) ≤ qc + -ql by linarith)
    · rw [hre]
      refine sub_eq_zero.1 (fam_eq_zero hG (fun α => ∃ a, rep a = α) (fun χ => by
        obtain ⟨a, mu, h⟩ := hcov χ; exact ⟨rep a, mu, ⟨a, rfl⟩, h⟩) _ fun α ⟨a₀, ha⟩ j => ?_)
      subst ha
      rw [sub_eq_add_neg, DVR.add_f, DVR.neg_f, comp, chart_of_point hL (s.s (rep a₀)) (fun i => gF D.toPre F (c a₀ i))
        (bF a₀) (hc a₀) j, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Equiv.symm_apply_apply, div_mul_cancel₀ _ (hlam0 a₀), sub_self]
  · rintro ⟨c, hcv, rfl⟩
    refine (n1a V ϖ hϖ D Q hQ F v hv k hk S hS _ 0).2 fun α hα => ?_
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hα
    rw [zero_add]
    refine ⟨k ^ D.toPre.P.g, fun i => c (e (a₀, i)) * lam a₀, b a₀, bF a₀,
      fun i => secScal_of_sval hL fun y J hJ => ?_, fun i => ?_, fun j => ?_⟩
    · rw [Category.id_comp]; exact (hbF _ _ y J hJ).symm
    · rw [AddValuation.map_mul]
      calc (((Q (rep a₀) : ℚ) / k : ℚ) : WithTop ℚ) = 0 + (((Q (rep a₀) : ℚ) / k : ℚ) : WithTop ℚ) := (zero_add _).symm
        _ ≤ v (c (e (a₀, i))) + v (lam a₀) := add_le_add (hcv _) (hql a₀)
    · rw [hre, comp]; rfl

private theorem repsX_statement : RepsXSt := by
  intro X _ _ _ k hk
  set b := Module.finBasis ℤ X
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun a => b.equivFun.symm fun i => ((a i : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro χ
    refine ⟨fun i => ⟨(b.equivFun χ i % k).toNat, ?_⟩, b.equivFun.symm fun i => b.equivFun χ i / k, ?_⟩
    · have h1 := Int.emod_nonneg (b.equivFun χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (b.equivFun χ i) hk0
      omega
    · apply b.equivFun.injective
      ext i
      simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')]
      first
        | exact Int.emod_add_mul_ediv _ _
  · intro a a' mu mu' h
    funext i
    have h' := congrArg (fun x => b.equivFun x i) h
    simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at h'
    have e1 : ((a i : ℕ) : ℤ) = (((a i : ℕ) : ℤ) + k * b.equivFun mu i) % k := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a i).isLt)]
    have e2 : ((a' i : ℕ) : ℤ) = (((a' i : ℕ) : ℤ) + k * b.equivFun mu' i) % k := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a' i).isLt)]
    have e3 : ((a i : ℕ) : ℤ) = ((a' i : ℕ) : ℤ) := by rw [e1, e2, h']
    exact Fin.ext (by exact_mod_cast e3)
  · intro x y h
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ] at h
    exact smul_right_injective X hk0.ne' h

private theorem ceil_statement : CeilSt := by
  intro F _ v π hπ hF q
  classical
  have hfin : ∀ x : F, x ≠ 0 → ∃ t : ℚ, (t : WithTop ℚ) = v x := fun x hx =>
    WithTop.ne_top_iff_exists.mp (v.top_iff.not.mpr hx)
  have hπ1 : v π = ((1 : ℚ) : WithTop ℚ) := by rw [hπ, WithTop.coe_one]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hπ
    first
      | simp at hπ
  have hpow : ∀ (x : F) (t : ℚ) (k : ℕ), v x = t → v (x ^ k) = ((k * t : ℚ) : WithTop ℚ) := by
    intro x t k ht
    rw [v.map_pow, ht, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hinv : ∀ x : F, x ≠ 0 → ∀ t : ℚ, v x = t → v x⁻¹ = ((-t : ℚ) : WithTop ℚ) := by
    intro x hx t ht
    obtain ⟨s, hs⟩ := hfin x⁻¹ (inv_ne_zero hx)
    have h1 : v (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, v.map_one]
    rw [v.map_mul, ht, ← hs, ← WithTop.coe_add] at h1
    have h2 : t + s = 0 := by exact_mod_cast h1
    rw [← hs]
    congr 1
    linarith
  have hvz : ∀ m : ℤ, v (π ^ m) = ((m : ℚ) : WithTop ℚ) := by
    intro m
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · rw [zpow_natCast, hpow π 1 k hπ1]
      congr 1
      push_cast
      ring
    · rw [zpow_neg, zpow_natCast, hinv _ (pow_ne_zero _ hπ0) _ (hpow π 1 k hπ1)]
      congr 1
      push_cast
      ring
  rcases hF with hac | ⟨d, hd, hval⟩
  · obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq (π ^ q.num) q.den_pos
    have hl0 : l ≠ 0 := by
      intro h
      rw [h, zero_pow q.den_pos.ne'] at hl
      exact zpow_ne_zero _ hπ0 hl.symm
    obtain ⟨t, ht⟩ := hfin l hl0
    have h1 := hpow l t q.den ht.symm
    rw [hl, hvz] at h1
    have h2 : (q.num : ℚ) = q.den * t := by exact_mod_cast h1
    have h3 : t = q := by
      have hd0 : (q.den : ℚ) ≠ 0 := by positivity
      rw [← Rat.num_div_den q, h2]
      field_simp
    refine ⟨l, hl0, fun x => ?_⟩
    rw [← ht, h3]
  · have hd0 : (0 : ℚ) < d := by exact_mod_cast hd
    have hd0' : (d : ℚ) ≠ 0 := hd0.ne'
    let P : ℤ → Prop := fun n =>
      (∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) ∧ q ≤ (n : ℚ) / d
    obtain ⟨n0, ⟨⟨l, hl0, hl⟩, hq⟩, hmin⟩ := Int.exists_least_of_bdd (P := P)
      ⟨⌊q * d⌋, fun z hz => by
        have h4 := hz.2
        rw [le_div_iff₀ hd0] at h4
        have h5 : (⌊q * d⌋ : ℚ) ≤ z := le_trans (Int.floor_le _) h4
        exact_mod_cast h5⟩
      ⟨⌈q⌉ * d, ⟨π ^ ⌈q⌉, zpow_ne_zero _ hπ0, by
          rw [hvz]
          congr 1
          push_cast
          field_simp⟩, by
        push_cast
        rw [mul_div_assoc, div_self hd0', _root_.mul_one]
        exact Int.le_ceil q⟩
    refine ⟨l, hl0, fun x => ⟨fun hx => ?_, fun hx => le_trans ?_ hx⟩⟩
    · by_cases hx0 : x = 0
      · rw [hx0, v.map_zero]
        exact le_top
      · obtain ⟨m, hm⟩ := hval x hx0
        have hPm : P m := ⟨⟨x, hx0, hm⟩, by rw [hm] at hx; exact_mod_cast hx⟩
        have h6 := hmin m hPm
        have h6' : (n0 : ℚ) ≤ m := by exact_mod_cast h6
        have h7 : (n0 : ℚ) / d ≤ (m : ℚ) / d := by gcongr
        rw [hl, hm]
        exact_mod_cast h7
    · rw [hl]
      exact_mod_cast hq

theorem uu (hL : Laws) (hT : TwistBaseChangeStatement) : UUStatement := by
  exact uu_of hL.globalFns hT repsX_statement ceil_statement

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt =====
