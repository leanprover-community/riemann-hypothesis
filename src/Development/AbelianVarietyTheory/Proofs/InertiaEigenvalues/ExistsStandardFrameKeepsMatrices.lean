module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead



noncomputable section

namespace GlobalTheory.MtRead.IdFrameStd

variable {D : D7}


open GlobalTheory.StdFrameExist in
theorem exists_idFrame_of (hF : D.host.F = maximalRealSubfield D.host.E) (V : HSp D) (hg : V.gram = 1)
    (hV : Seed.FrmC.StdLat V) (n : ℕ) (hn : V.rank = n) :
    ∃ P : principalLevelFrame.RowPsi V n, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  subst hn
  have hO : IsOrthF V (1 : GL (Fin V.rank) (Lev.EAf D)) := by
    show Formalism.UG.cT (sgA D) (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * gA V * 1 = 1
    have : gA V = 1 := by
      show V.gram.map _ = 1
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]
  have hI : IntM (SI D) ((1 : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := fun i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact (SI D).one_mem
    · exact (SI D).zero_mem
  refine ⟨rowPsi V 1 hO, ⟨rfl, fun κ a b => ?_⟩, stdFrame_rowPsi hF hV hO hI (by rw [inv_one]; exact hI)⟩
  rw [← GlobalTheory.HeckeTrans.finE_unswap]
  show (Formalism.IndefR.Lev.finE V (psiF V 1 hO κ)).1.map _ a b = _
  rw [finE_psiF, inv_one, mul_one, one_mul]
  rfl

theorem exists_idFrame : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j →
    ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  intro D hF j hV
  have hL := (GlobalTheory.Equiv.StdSpace.lattice_clause_iff (Vc D j)).1 hV.2
  have hS : Seed.FrmC.StdLat (Vc D j) := fun x => by
    rw [hL]
    exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  exact exists_idFrame_of hF (Vc D j) hV.1 hS D.R.nV (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc j).1

end GlobalTheory.MtRead.IdFrameStd

end
