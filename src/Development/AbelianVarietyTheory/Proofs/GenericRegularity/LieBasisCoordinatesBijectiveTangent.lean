module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

@[expose] public section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem isTangent_of_isLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {cv : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (hv : ∀ i, IsTangent (v i)) (h : IsLieComb cv v w) :
    IsTangent w := by
  rw [(Chart.isLieComb_iff cv v w).1 h, ← Chart.isTan_iff]
  refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
  intro a ha
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
  exact Chart.isTan_scale (cv i) ((Chart.isTan_iff _).2 (hv i))

theorem vec_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ
  obtain ⟨v, hv, hb, -⟩ := M.lie R f Λ.t' Λ.m2
  have key : ∀ cv w, Λ.Vec cv w ↔ ∃ u', IsLieComb cv v u' ∧ u'.left ≫ Λ.m1.φ = w := by
    intro cv w
    constructor
    · rintro ⟨v', u', h1, h2, h3⟩
      have e : v' = v := funext fun j => Chart.inj_over Λ.m2.cart ((h1 j).trans (hv j).symm)
      exact ⟨u', e ▸ h2, h3⟩
    · rintro ⟨u', h2, h3⟩
      exact ⟨v, u', hv, h2, h3⟩
  refine ⟨fun cv => ?_, fun cv w h => ?_, fun w hw => ?_⟩
  · refine ⟨(Chart.prodPts cv v).left ≫ Λ.m1.φ, (key _ _).2 ⟨_, (Chart.isLieComb_iff cv v _).2 rfl, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨u', h2, h3⟩ := (key _ _).1 hw
    rw [← h3, (Chart.isLieComb_iff cv v _).1 h2]
  · obtain ⟨u', h2, rfl⟩ := (key _ _).1 h
    refine ⟨?_, (Chart.tan_push Λ.m1.cart u').1 (isTangent_of_isLieComb hb.1 h2)⟩
    have e1 : Λ.m1.φ ≫ Xo.univ.t.G.hom = Λ.t'.G.hom ≫ x := Λ.m1.cart.1.w
    have e2 : u'.left ≫ Λ.t'.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w u'
    rw [Category.assoc, e1, ← Category.assoc, e2]
  · let u' : epsR R ⟶ Λ.t'.G :=
      Over.homMk (Λ.m1.cart.1.lift w (spMap (algebraMap R (DualNumber R))) hw.1) (Λ.m1.cart.1.lift_snd _ _ _)
    have hu : u'.left ≫ Λ.m1.φ = w := Λ.m1.cart.1.lift_fst _ _ _
    have ht : IsTangent u' := (Chart.tan_push Λ.m1.cart u').2 (by
      have := hw.2
      rw [← hu] at this
      exact this)
    obtain ⟨cv, hc, huniq⟩ := hb.2 u' ht
    refine ⟨cv, (key _ _).2 ⟨u', hc, hu⟩, fun cv' h' => ?_⟩
    obtain ⟨u'', h2, h3⟩ := (key _ _).1 h'
    have e : u'' = u' := Chart.inj_over Λ.m1.cart (h3.trans hu.symm)
    exact huniq cv' (e ▸ h2)

end GlobalTheory.Reg
