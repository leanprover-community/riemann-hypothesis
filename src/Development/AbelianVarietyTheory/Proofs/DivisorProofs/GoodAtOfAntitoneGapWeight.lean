module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  set_option synthInstance.maxHeartbeats 200000 in
  refine ⟨hasGram_nrm_of_good D T j Y e o hY G', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

end GlobalTheory.CovTop.ShiftGood

end
