module

public import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_genericPoint_hom (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (G : Over (Sp O)) [GrpObj G] (hsep : IsSeparated G.hom)
    (A : Over (Sp C)) [GrpObj A] (gen : A.left ⟶ G.left)
    (h : IsGrpPullback A G (spMap (algebraMap O C)) gen) :
    ∃ j : (algOver O O ⟶ G) →* Pts A, Function.Injective j ∧
      ∀ P z, z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j P := by
  have hid : spMap (algebraMap O O) = 𝟙 (Sp O) := by
    simp [spMap]
  let e₀ : (Over.mk ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).hom ≫ spMap (algebraMap O C)) : Over (Sp O)) ⟶ algOver O O :=
    Over.homMk (spMap (algebraMap O C)) (by
      change spMap (algebraMap O C) ≫ spMap (algebraMap O O) = 𝟙 _ ≫ spMap (algebraMap O C)
      rw [hid, Category.comp_id, Category.id_comp])
  have hw : ∀ P : algOver O O ⟶ G,
      (spMap (algebraMap O C) ≫ P.left) ≫ G.hom = 𝟙 (Sp C) ≫ spMap (algebraMap O C) := fun P => by
    have := Over.w (e₀ ≫ P)
    exact this
  let j₀ : (algOver O O ⟶ G) → Pts A := fun P =>
    Over.homMk (h.1.lift (spMap (algebraMap O C) ≫ P.left) (𝟙 (Sp C)) (hw P)) (h.1.lift_snd _ _ _)
  have hj : ∀ P, (j₀ P).left ≫ gen = spMap (algebraMap O C) ≫ P.left := fun P => h.1.lift_fst _ _ _
  have key : ∀ (P : algOver O O ⟶ G) (z : Pts A),
      z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j₀ P := fun P z => by
    constructor
    · intro hz
      refine Over.OverMorphism.ext (h.1.hom_ext (hz.trans (hj P).symm) ?_)
      exact (Over.w z).trans (Over.w (j₀ P)).symm
    · rintro rfl
      exact hj P
  have hmul : ∀ P Q, j₀ (P * Q) = j₀ P * j₀ Q := fun P Q => by
    refine ((key _ _).1 ?_).symm
    have e := h.2 _ (j₀ P) (j₀ Q) (e₀ ≫ P) (e₀ ≫ Q) (hj P).symm (hj Q).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  refine ⟨MonoidHom.mk' j₀ hmul, fun P Q hPQ => ?_, key⟩
  have hPQ' : j₀ P = j₀ Q := hPQ
  haveI : IsDomain O := hinj.isDomain _
  haveI : IsDominant (spMap (algebraMap O C)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O C)).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine Over.OverMorphism.ext ?_
  refine ext_of_isDominant_of_isSeparated (X := Sp O) G.hom ?_ (spMap (algebraMap O C)) ?_
  · exact (Over.w P).trans (Over.w Q).symm
  · exact (hj P).symm.trans (by rw [hPQ']; exact hj Q)

end GlobalTheory.ChTor
