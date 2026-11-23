module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumEpsPairingSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDatumBiconnOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnectedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatricesStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FarguesExactness.FarguesExactOfPrismatic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta

@[expose] public section

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace UpperTheory.Lit

theorem prismaticDieudonneHodge : GlobalTheory.Published.PrismaticDieudonneHodge := by
  intro p _ C _ _ _ v O _ _ hv _ _ ε hε
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hs : IsPrimitiveSystem ε := fun n => GlobalTheory.Dieudonne.isPrimitiveRoot_untilt_root hε n
  exact GlobalTheory.T.prismaticDieudonneHodge_of_hodgeTateDatum p C v O hv ε hs (GlobalTheory.T.pDivisibleGroup_datum_of_connected_dual_connected p C v O hv ε hs
    (hasDatum_biconn_of GlobalTheory.BRing.exists_bFrame GlobalTheory.QLog.WindowMat.window_matrices GlobalTheory.T.window_lift_to_fontaineAinf_matrices
      GlobalTheory.DatumOfMatrices.hasDatum_of_matrices p C v O hv ε hs))

theorem farguesExact : GlobalTheory.CompanionTheory.Ar.HT.FarguesExact :=
  PositivityTheory.Tls2.Jfarg.farguesExact_of_hodge prismaticDieudonneHodge

end UpperTheory.Lit

end
