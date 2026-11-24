module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v),
        ∃ a : AE D, IsSplitIdem D a ∧ ∀ z : AE D, At (evFin D.host.F v) z → piW t z = 0 → a * z = z := by
  intro D v t
  refine ⟨GlobalTheory.EmbChart.idem (t.comp D.sp.cm.sig), GlobalTheory.EmbChart.isSplitIdem_idem _, fun z hz h0 => ?_⟩
  have h1 : (1 - GlobalTheory.EmbChart.atPlace v (1 : Fv D.host.F v)) • z = 0 :=
    hz _ (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero, Algebra.smul_def] at h1
  have h2 : z = GlobalTheory.EmbChart.tensAt D.host.E v (1 * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) :=
    h1.trans (GlobalTheory.EmbChart.tensAt_mul_right v 1 z)
  have h3 : GlobalTheory.AdelicU.splitIdem (GlobalTheory.AdelicU.isCMExt_host D) t * GlobalTheory.AdelicU.compFin D.host.F D.host.E v z = 0 :=
    (GlobalTheory.AdelicU.splitProj_eq_zero_iff _ t _).1 h0
  rw [GlobalTheory.EmbChart.idem_mul, GlobalTheory.AdelicU.splitIdem_comp, sub_mul, h3, sub_zero]
  exact h2.symm
