module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem LevelPoints.comp_act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h0 : t.act.act 0 = 1 := by simpa using h
    rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem exists_levPt_eq_of_killedBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (t : ptO Xo yF.x ⟶ Xo.univ.t.G), KilledBy Xo l.Mb t → ∃ a : Dw.La, levPt Xo yF.x a = t := by
  intro E _ _ _ H Dw l Xo c F _ _ _ yF t ht
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom F yF.x (Spec.preimage (yF.x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hpow : t ^ l.M = 1 := by
    rw [← LevelPoints.comp_act_natCast]
    exact ht _ (LevelPoints.natCast_mem l)
  obtain ⟨a, ha⟩ := (I.onto l.M hM t).1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  refine ⟨v • a, (hI _ (Submodule.smul_mem_smul hv Submodule.mem_top)).trans ?_⟩
  have h1 : I.ev l.M (u • a) = 1 := by
    rw [I.lin, ha]
    exact ht u hu
  have h2 := I.add l.M (u • a) (v • a)
  rw [← add_smul, huv, one_smul, h1, _root_.one_mul] at h2
  exact h2.symm.trans ha

end GlobalTheory
