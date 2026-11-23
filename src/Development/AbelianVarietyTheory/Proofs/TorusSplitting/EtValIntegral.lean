module

public import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FormAtOfClause
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaInt

theorem etVal_integral :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), (Formalism.MainNotions.ModuliIntegralCharts.H1.EtVal (recPJ h j hj) i η ↔ Formalism.L2.Pj.EtVal h j hj i η) ∧ (∀ la (y : (recPJ h j hj).Pt la), 0 ≤ (recPJ h j hj).phiC la y) ∧ (Formalism.L2.Pj.EtVal h j hj i η → IntAlg η.1 ∧ η ∈ (recB h.toLawsCore).Mlat j (wEt D j i)) := by
  intro D T h j hj i η
  refine ⟨Iff.rfl, GlobalTheory.EtaValuationTest.phiC_nonneg _, fun hv => ?_⟩
  have hm : η ∈ (recB h.toLawsCore).Mlat j (wEt D j i) :=
    GlobalTheory.EtaValuationTest.mem_Mlat (recPJ h j hj) i η hv
  refine ⟨?_, hm⟩
  have h0 := ((recPJ h j hj).Mlat_eq _ η).1 hm
  refine (nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) η.1).2 fun la y => ?_
  exact le_of_le_of_eq (h0 la y) (recPJ_vAt_inc h j hj la y _ η)

end GlobalTheory.EtaInt
