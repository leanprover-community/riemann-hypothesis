module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.finiteHeisenbergTranslate_selfDualVacuum_fockJets : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E))
    (κ : ℂ) (F : WO (G.pS p) (G.pT p) → ℂ), SD D Ls → SD D Lt →
    Differentiable ℂ (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) →
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) F →
    (∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p F (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p) z)) →
    ∀ (n : ℕ), 0 < n → ∀ w : WO (G.pS p) (G.pT p), n • w ∈ latO _ _ (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) (fun _ => True) →
    ∃ (ζ : Qbar) (s : VC D (G.pS p).rank (G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ n • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt ∧
    ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p (heisO W.ψ _ _ w F) (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK S.Z.δ) s
          (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) z)) := by
  first | exact @GlobalTheory.HeisTrans.main | exact GlobalTheory.HeisTrans.main | (intros; apply GlobalTheory.HeisTrans.main <;> assumption)
