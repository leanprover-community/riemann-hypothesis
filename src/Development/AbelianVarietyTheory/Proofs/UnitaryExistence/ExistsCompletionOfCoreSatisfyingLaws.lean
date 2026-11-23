module

public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SChartsAndTransferOfGoodLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOneStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModelsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocalDataAtConcretePointsExistStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndNab
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Member

theorem exists_completion_of_core_satisfying_laws : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Core D), LawsCore T → (∀ j, 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) → (∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c) → (∀ j, InR D j → ∀ (_ : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab → ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) ∧ (j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c nab)) → ∃ T' : Top D, LawsP T' ∧ T'.toCore = T := by
  intro hC D T hT hpq hK hth
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.localDataAtConcretePoints_exist D T.Q hT.pins hpq
  have hnab := fun j => GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  choose st nab hN using hnab
  have hgood := (GlobalTheory.T.level_good_and_half_eq_prime_product D T.Q.H T.Q.l hT.pins.1.2.1 hT.pins.2.1.1).1
  have hreg := fun j => GlobalTheory.Reg.sCharts_and_transfer_of_good_level GlobalTheory.T.compactifiedModuli_partOne GlobalTheory.Moduli.moduli_scheme_exists
    D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (hpq j) hgood
  refine ⟨{ toCore := T, G := G, nab := nab,
            dδ := fun j n => noDelta (T.Q.Xo j) T.Q.c (nab j) (GlobalTheory.ObjLower.sabId (T.Q.Xo j).univ.t) n }, ?_, rfl⟩
  exact
    { toLawsCore := hT
      allTest := fun j _ => GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange D.host.E T.Q.H (T.Q.Dw j)
        T.Q.l (T.Q.Xo j) T.Q.c
      reg := fun j _ => (Formalism.L2.PjFree.regP_ofPj (T.U j)).1 ((hreg j).2.1 D.R.r _)
      datum_condition := h1
      tower := h2
      hasData_condition := h3
      points_condition := h4
      lattice_condition := h5
      bc66 := h6
      datIndep := fun j _ _ => GlobalTheory.T.latticePeriodForm_independent_of_models D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
      nabPin := fun j _ => ⟨st j, hN j⟩
      nabUniq := fun j _ => Formalism.MainNotions.ModuliIntegralCharts.H1.nabUniq_of_chartIndep2 hC (T.Q.Xo j) T.Q.c
      thTot := fun j _ => @GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 hC D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l
        (T.Q.Xo j) T.Q.c (st j) (nab j) (hN j)
      thCusp := fun j hj => (hth j hj (st j) (nab j) (hN j)).1
      thNe := fun j h1 h2 => (hth j ⟨h1, h2.le⟩ (st j) (nab j) (hN j)).2 h2
      kPsi := hK }

end GlobalTheory.Member
