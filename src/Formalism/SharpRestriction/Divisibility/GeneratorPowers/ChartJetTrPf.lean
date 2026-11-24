module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetSubSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)


theorem chartJetTr_of (hTan : ChartJetTanSt Xo c) (hBas : ChartJetBasisSt Xo c) : ChartJetTrSt Xo c := by
  intro T io y I d FT actT tgT uvecT xT hbas hch hdir
  letI := io.toAlgebra
  refine ⟨xU I xT, xP I xT, ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_,
    hTan T io y I d FT actT tgT uvecT xT hbas hch hdir, hBas T io y I d FT actT tgT uvecT xT hbas hch hdir⟩,
    fun m => xL_fst I xT m, fun m => rfl⟩
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = (spMap (algebraMap T.Fr T.Fr) ≫ y.1.x) ≫ η[Xo.univ.t.G].left
    rw [← Category.assoc, xL_zero I xT hch.zero m, unit_push I.m1.cart, spMap_alg_self, Category.id_comp]
  ·
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT (m + 1) ≫ I.m1.φ = xL I xT m ≫ I.m1.φ
    rw [← Category.assoc, xL_trunc I xT hch.trunc m]
  ·
    simp only [psTrunc_map]
    let W : (jO y.1 d m 2) ⟶ Over.mk ((jOG (𝟙 (Sp T.Fr)) d m 2).hom ≫ y.1.x) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (spMap _ ≫ 𝟙 _) ≫ y.1.x = spMap _ ≫ y.1.x
        simp)
    have hj : ∀ i : Fin 2, jpt y.1 d (xU I xT) m i =
        W ≫ pushHom I.m1.cart _ (jptG I.t' (𝟙 (Sp T.Fr)) d (xP I xT) m i) := fun i =>
      Over.OverMorphism.ext (by
        show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
        simp)
    rw [hj 0, hj 1, ← MonObj.comp_mul, ← map_mul, ← xP_law I xT FT m (hch.law m)]
    apply Over.OverMorphism.ext
    show spMap _ ≫ xL I xT m ≫ I.m1.φ = 𝟙 _ ≫ (spMap _ ≫ xL I xT m) ≫ I.m1.φ
    simp
  ·
    simp only [psTrunc_map]
    apply Over.OverMorphism.ext
    show (xL I xT m ≫ I.m1.φ) ≫ (Xo.univ.t.act.act a).left = spMap _ ≫ xL I xT m ≫ I.m1.φ
    rw [Category.assoc, ← I.m1.act a, ← Category.assoc, xL_act I xT (actT a) a m (hch.act m a), Category.assoc]

end Formalism.MainNotions.ModuliIntegralCharts.H1
