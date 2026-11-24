module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumPairEqAdelicDatumTwoPointsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReaderLevelBadPrimesCoprimeResidueCharStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Xc.xiM_eq_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb La' Lb' hab hab'
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hj1 : j + 1 ≤ D.R.m := hj
  funext z
  rw [GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) La La' z, GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) Lb Lb' z]
  have hc : J.chart std j (Nat.le_of_succ_le hj1) La = J.chart std j (Nat.le_of_succ_le hj1) Lb := by
    obtain ⟨h1, h2, h3, -⟩ := hab
    rcases La with ⟨c, a⟩
    rcases Lb with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j _ c a b h1 h2
  have hc' : J.chart std (j + 1) hj1 La' = J.chart std (j + 1) hj1 Lb' := by
    obtain ⟨h1, h2, h3, -⟩ := hab'
    rcases La' with ⟨c, a⟩
    rcases Lb' with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS (j + 1) _ c a b h1 h2
  rw [hc, hc']
  refine congrFun (S.law.away j hj1 _ _ (J.pt std j _ Lb) (J.pt std (j + 1) hj1 Lb') (J.pt std j _ La) (J.pt std (j + 1) hj1 La') ?_) _
  intro v' hv'
  have hne : v' ≠ ((A0 J).pl v).1 := fun h => (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hS).2.2.1 v' hv' (h ▸ ((A0 J).pl v).2)
  exact ⟨(GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j _ La Lb hab).1 v' hne, (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v (j + 1) hj1 La' Lb' hab').1 v' hne⟩
