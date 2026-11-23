module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaValueNaturalField
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem evI_eq_thExpr_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ) (xx : Fin n → Dw.La) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x)), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) → ∀ f, IsThRule Xo c nab xx Pp f → algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y F _ _ φ hφ yF hm a n xx Pp hP Fs hFs f hf
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hyT := y.2.1
  unfold evI evR evalAt
  rw [dite_eq_left hyT]
  have hm0 := hyT.choose_spec.choose_spec.choose_spec
  have hv0 := hf hyT.choose hyT.choose_spec.choose_spec.choose
  have hvF : ThValAt Xo c nab yF xx Pp (thExpr Xo c nab yF Pp Fs) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id c.F F, yF, Fs, ?_, GlobalTheory.FramedBaseChange.refl yF, hFs, rfl⟩
  · have key := GlobalTheory.ThetaField.thetaValue_natural_field E H Dw l Xo c nab hnab _ F (φ.comp _) _ yF
      (GlobalTheory.FramedBaseChange.trans _ φ hm0 hm) a n xx Pp hP _ _ hv0 hvF
    refine Eq.trans ?_ key
    exact (congrArg (fun g : T.Fr →+* F => g _) hφ).symm
  · exact RingHom.FaithfullyFlat.of_bijective Function.bijective_id

end GlobalTheory.PtTie
