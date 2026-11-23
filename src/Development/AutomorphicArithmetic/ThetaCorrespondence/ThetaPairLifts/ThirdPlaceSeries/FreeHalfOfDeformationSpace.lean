module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPermutedDirectSumComplexificationStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsFreeHalfLiftOfNeat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitDeformationLift
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
noncomputable section
namespace GlobalTheory.DefHalf

theorem halfH_acts_freely_on_internal_sum_decomposition : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  intro hP hG
  have h1 := _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index hP hG
  have h2 := _root_.GlobalTheory.T.exists_isInternal_free_permuted_thirdPlace hP hG
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine Closed.imp (h1.and h2) ?_
  rintro eps Fm CH - ⟨⟨C1, -, x1, ha1⟩, ⟨C2, -, x2, ha2⟩⟩
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi k => ?_⟩
  have a1 := ha1 x hx (le_trans (le_max_left _ _) hle) ι p hp i hi k
  have a2 := ha2 x hx (le_trans (le_max_right _ _) hle) ι p hp i hi hp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k)
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) a1
  obtain ⟨X, hX, hdX, hact, A, hfr, hint, hperm⟩ := a2
  letI := ((p.R.toRealDat.FW i)).towKs
  obtain ⟨n, b, hbW, hbK, hbsK, hbL, hbsL⟩ := p.fw.ks i
  have hK := (p.rhoGeo i).1 (fun g f hf => _root_.GlobalTheory.DefHalf.keeps_alt p i hp.1 g f hf)
  have he : ∀ g f, (((p.fw.e i) (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1 g f) : (p.R.FW i).WK) : Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) =
      (p.R.FW i).ρ g ((p.fw.e i) f) := by
    intro g f
    obtain ⟨hf, h⟩ := hK g f
    rw [← h]
    rfl
  obtain ⟨A', hint', hperm'⟩ := GlobalTheory.T.transport_permuted_directSum_complexification p.T.Q.c.F (Fm.D x ι).what₂.LL (Fin (p.R.nW i) → (Fm.D x ι).what₂.LL) (CF p i)
    (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) p.P.Gp X (Fm.D x ι).what₂.embLL (p.R.FW i).WK n b hbW hbK hbsK hbL hbsL
    (p.fw.e i) (p.R.FW i).ρ (p.R.FW i).chi (_root_.GlobalTheory.DefHalf.groupActionOnCoefficients p i hp.1) he
    (((p.R.eG.trans p.cG).symm.toMonoidHom).comp (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k).subtype) A hint hperm
  exact ⟨X, hX, hdX, hact, A', hfr, hint', fun h y v hv => hperm' h y v hv⟩
end GlobalTheory.DefHalf
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.halfH_free_action_and_isInternal_repAt_mem : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) X)
      (A : X → Submodule ℂ (GlobalTheory.DefRead.VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k) (y : X), ∀ v ∈ A y,
        GlobalTheory.DefRead.repAt p i (h : G0g (Fm.D x ι).nd) v ∈ A (h • y) := by
  exact @_root_.GlobalTheory.DefHalf.halfH_acts_freely_on_internal_sum_decomposition
end
end
