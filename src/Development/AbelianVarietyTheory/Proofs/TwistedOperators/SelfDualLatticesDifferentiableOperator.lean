module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
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

noncomputable section

namespace GlobalTheory.MovedDict

theorem negGA_mem_GfC' {D : D7} (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem jetTab_heisO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ f : WO (G.pS p) (G.pT p) → ℂ,
    IsThetaFunO W.ψ _ _ f → ∀ w : WO (G.pS p) (G.pT p), ∀ (x : FinPt G p.small) (y : FinPt G p.big)
    (mon : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ),
    jetTab W B p (heisO W.ψ _ _ w f) x y mon = fockIn W B p (heisO W.ψ _ _ (actO _ _ (G.toPair p x y).1 (G.toPair p x y).2 w)
      (W.om p (G.toPair p x y) f)) (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) 0 := by
  intro D T L sc G W B p hp f hf w x y mon
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have mem : (G.toPair p x y).1 ∈ GfC (G.pS p) ∧ (G.toPair p x y).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | mu t i j => exact ⟨x.2, y.2⟩
    | core i => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | top t j => exact ⟨x.2, y.2⟩
  have hth := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all W.ψ_std hf w
  have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) hom W.θ W.θ_is _ mem.1 _ mem.2
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) _ (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) hth
  rw [hom.om_heis _ _ w f hf] at e
  simp only [jetTab, GlobalTheory.FunObj.kerFin, GridData.Weil.ker, thetaKO, fockIn]
  rw [e]

theorem actO_nsmul {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (n : ℕ) (w : WO S T) :
    actO S T g h (n • w) = n • actO S T g h w := by
  unfold actO
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, ih]

end GlobalTheory.MovedDict

end
