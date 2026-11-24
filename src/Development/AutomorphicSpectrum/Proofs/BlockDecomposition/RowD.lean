module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.ZUnf

section Rows

variable {K : Type} [Field K] {n ρ p : ℕ}

def zinc (hn : ρ + p = n) : (Fin ρ → K) →ₗ[K] (Fin n → K) where
  toFun u i := Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm i)
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp
  map_smul' c u := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
    rcases j with j | j <;> simp

def wM (hn : ρ + p = n) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 0 0 0 1) (bl hn 1 0 0 0) (bl hn (-1) 0 0 0) (bl hn 0 0 0 1)

def nM (hn : ρ + p = n) (ζ : Matrix (Fin ρ) (Fin ρ) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 1 (bl hn ζ 0 0 0) 0 1

def sM (hn : ρ + p = n) (σ : K →+* K) (η : Matrix (Fin ρ) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 η 0 1) 0 0 (bl hn 1 0 (-cT σ η) 1)

def eM (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) : Matrix (Fin (n + n)) (Fin (n + n)) K :=
  blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d)

def rowC (hn : ρ + p = n) (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-1) (-(η * a)) 0 c

def rowD (hn : ρ + p = n) (σ : K →+* K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K)
    (b d : Matrix (Fin p) (Fin p) K) : Matrix (Fin n) (Fin n) K :=
  bl hn (-ζ) (-(η * b)) (-cT σ η) d

end Rows

variable {D : D7} {n ρ p : ℕ}

def zKer (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin ρ → D.host.E) :=
  (cellKer x).comap (zinc hn)

end GlobalTheory.CompanionTheory.ZUnf
