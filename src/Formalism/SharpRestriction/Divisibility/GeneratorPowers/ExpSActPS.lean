module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartActionPoint
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ScaleGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GmHomAt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem expS_actPS {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d) S)
    (hg : MvPowerSeries.constantCoeff g = 0) (k : 𝓞 E) :
    MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (Germ.FB.expS S (-(compL φ g))) =
      Germ.FB.expS S (-(compL (φa c φ k) g)) := by
  have hb : MvPowerSeries.HasSubst (actPS (Dw := Dw) (S := S) c k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by simp [actPS]
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hφ p.2
  have h0 : MvPowerSeries.constantCoeff (-(compL φ g)) = 0 := by
    rw [map_neg, ExpGB.const_compL φ hφ g, hg, neg_zero]
  have hcomp : MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (-(compL φ g)) =
      -(compL (φa c φ k) g) := by
    rw [← MvPowerSeries.coe_substAlgHom hb, map_neg, MvPowerSeries.coe_substAlgHom hb]
    unfold compL φa
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  unfold Germ.FB.expS PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0).const hb]
  simp only [hcomp]

theorem val_e (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (u m)) *
        (val C.wP ((ptm C ![φ] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φ, φa c φ H.w0] m).left z J) := by
  have hX : actP (Dw := Dw) (S := S) c 1 = fun p => MvPolynomial.X p := by
    funext p
    simp [actP]
  have hid : jetSubstP m (actP (Dw := Dw) (S := S) c 1) = AlgHom.id S _ := by
    rw [hX]
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [jetSubstP, jetMap, liftJet, Ideal.Quotient.lift_mk, MvPolynomial.aeval_X_left] <;> rfl
  have hP : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  have hφ1 : φa c φ 1 = φ := by
    funext j
    simp only [φa, hP]
    exact congrFun MvPowerSeries.subst_self (φ j)
  have hu : Units.map (AlgHom.id S (Jet S (Fin 1 × Fin (dL Dw)) m)).toMonoidHom (u m) = u m :=
    Units.ext rfl
  have h1 := val_eAt C φ hφ hact τ u hτc m 1 z J hJ
  rw [hφ1, _root_.mul_one] at h1
  unfold eAt at h1
  rw [val_pull, hid, homAt_id, Over.id_left, Category.comp_id, hu] at h1
  exact h1
  exact hJ

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
