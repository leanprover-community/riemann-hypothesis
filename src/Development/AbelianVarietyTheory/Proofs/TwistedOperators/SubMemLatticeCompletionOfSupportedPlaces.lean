module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.LatBridge

theorem cut_mem_latV {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop)
    (u : Fin S.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hu : u ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))) :
    AddMonoidHom.compLeft (GlobalTheory.HatLatV.cutHom P) (Fin S.rank) u ∈ latV S L P := by
  refine AddSubgroup.closure_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_) hu
  · obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]
        exact ha v
      · rw [zero_mul]
        exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      rw [one_mul]
      exact GlobalTheory.HatLatV.cut_tmul P a (x i)
  · rw [map_zero]
    exact (latV S L P).zero_mem
  · rw [map_add (f := _)]
    exact (latV S L P).add_mem hy hz
  · rw [map_neg]
    exact (latV S L P).neg_mem hy

theorem finPart_mul_cut {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (a : AE D) (ha : a ∈ idAt D P)
    (u : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (a * GlobalTheory.HatLatV.cut P u) = finPart D a * u := by

  have hfix := congrArg (finPart D) (GlobalTheory.HatLatV.cut_finPart P a ha)
  simp only [GlobalTheory.HatLatV.cut, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_lift] at hfix
  rw [map_mul]
  simp only [GlobalTheory.HatLatV.cut, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_lift]
  rw [← mul_assoc, mul_comm (finPart D a), hfix]




theorem sub_mem_hatL : ∀ (D : D7) (S : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) (L L' : GlobalTheory.FinPl.Lat S) (g : GA D S), g ∈ grpAt S P →
  (∀ y : Fin S.rank → AE D, y ∈ latV S L P → (mt S g - 1) *ᵥ y ∈ latV S L' P) →
  ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, (Lev.finE S g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L' := by
  intro D S P L L' g hg hmove x hx

  set u : Fin S.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j => Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F) (x j) with hu_def
  have hswap : ∀ j, Formalism.IndefR.Lev.swapAE D (u j) = x j := by
    intro j
    simp only [u, Formalism.IndefR.Lev.swapAE]
    generalize x j = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hu : u ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) := by
    rw [GlobalTheory.LevSplit.latHat_iff]
    convert hx using 1
    funext j
    exact hswap j

  have hI : ∀ i j, (Formalism.L2.Theta.mt S g - 1) i j ∈ idAt D P :=
    (GlobalTheory.FrameAt.mem_congGrp S (idAt D P) g).1 hg
  have hmem := GlobalTheory.LatVHat.latV_mem_hatL D S L' P _ (hmove _ (cut_mem_latV S L P u hu))
  have hcut : ∀ z, GlobalTheory.HatLatV.cutHom P z = GlobalTheory.HatLatV.cut P z := fun _ => rfl
  have hlhs : (Lev.finE S g).1 *ᵥ x - x = ((Formalism.L2.Theta.mt S g - 1).map (GlobalTheory.LevSplit.finSw D)) *ᵥ x := by
    rw [GlobalTheory.LevSplit.finE_val, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.sub_mulVec,
      Matrix.one_mulVec]
  rw [hlhs]
  convert hmem using 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    AddMonoidHom.compLeft_apply, Function.comp_apply, hcut]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finPart_mul_cut P _ (hI i j), map_mul, hswap]
  rfl

end GlobalTheory.LatBridge
