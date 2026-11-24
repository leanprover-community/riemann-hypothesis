module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesHasReaderLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLawsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hTie
  exact GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c')
    (GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
