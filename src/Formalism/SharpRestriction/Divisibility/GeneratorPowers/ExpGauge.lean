module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpAct
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CocChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ESecToUnit
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGJAd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGOPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGUPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhTwoValHolds
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SubstCoeRename
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem expGaugeOf_of (hA : ExpActOfSt) : ExpGaugeOfSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C htr φ hφ hx
  have hact : ∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (ExpGU.actPS (Dw := Dw) c a) (φ j) := hA E H Dw l Xo c S y C φ hφ
  obtain ⟨τ, u, _, hτc, hu, hgen, hof⟩ := ExpGA.exists_eG C φ hφ.const
  refine ⟨ExpGA.eG C φ τ u, ⟨hgen, fun m => ExpGB.trunc_eG C htr φ τ u hτc hu m,
    ExpGB.rig_eG C φ hφ.const τ u hτc hu, fun a => ?_⟩, hof⟩
  have hbb : H.bar (H.bar a) = a := by rw [← hs, ← hs, star_star]
  obtain ⟨wLa, hwa, hra⟩ := ExpGD.exists_adRel C a
  obtain ⟨wLb, hwb, hrb⟩ := ExpGD.exists_adRel C (H.bar a)
  obtain ⟨β, hβ, hβ0, hβv⟩ := ExpGE.exists_beta C.wP C.prim a hbb wLa hwa wLb hwb
  exact ⟨β, hβ, hβ0, fun m => ExpGL.coc_chart ExpGJPh1.phOneVal_holds ExpGJ.phTwoVal_holds ExpGJ.adVal
    ExpGU.unitId ExpGO.bqOrigin hs C φ hφ hx hact τ u hτc hu a wLa hra wLb hrb β hβv m⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge
