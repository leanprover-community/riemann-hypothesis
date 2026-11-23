module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LWMaj

variable {D : D7}

theorem unifLevel {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (C : Set (GA D S)) (hC : IsCompact C) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ g ∈ C, om (g, 1) f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  obtain ⟨U, hUo, hU⟩ := hf.level

  let a : GA D S → WO S T →+ WO S T := fun g =>
    { toFun := fun u => actO S T g⁻¹ 1 u
      map_zero' := by simp [actO]
      map_add' := fun u v => by simp [actO, Matrix.mul_add, Matrix.add_mul] }
  let U' : AddSubgroup (WO S T) := ⨅ g ∈ C, U.comap (a g)
  have hcont : Continuous fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2 := by
    simp only [actO, inv_inv]
    exact (continuous_const.matrix_mul continuous_snd).matrix_mul ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst)
  have hmem : ∀ u, u ∈ U' ↔ ∀ g ∈ C, actO S T g⁻¹ 1 u ∈ U := fun u => by
    rw [AddSubgroup.mem_iInf]
    exact forall_congr' fun g => by rw [AddSubgroup.mem_iInf]; rfl
  have hopen : IsOpen (U' : Set (WO S T)) := by
    have hn : C ×ˢ ({0} : Set (WO S T)) ⊆ (fun p : GA D S × WO S T => actO S T p.1⁻¹ 1 p.2) ⁻¹' U := by
      rintro ⟨g, u⟩ ⟨-, hu⟩
      simp only [Set.mem_singleton_iff] at hu
      subst hu
      simp [actO, U.zero_mem]
    obtain ⟨s, v, -, hv, hCs, h0v, hsv⟩ :=
      generalized_tube_lemma hC isCompact_singleton (hUo.preimage hcont) hn
    refine AddSubgroup.isOpen_of_mem_nhds U' (g := 0) ?_
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun u hu => ?_
    refine (hmem u).2 fun g hg => ?_
    have h := hsv (Set.mk_mem_prod (hCs hg) hu)
    rw [Set.mem_preimage] at h
    exact h
  refine ⟨U', hopen, fun g hg => ⟨hom.om_pres _ _ hf, fun u hu h0 => ?_⟩⟩
  have hu' : actO S T g⁻¹ 1 u ∈ U := by
    exact (hmem u).1 hu g hg
  have h0' : (actO S T g⁻¹ 1 u).map (infPart D) = 0 := by
    simp only [actO, Matrix.map_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  have h1 := hom.om_heis g 1 (actO S T g⁻¹ 1 u) f hf
  rw [hU _ hu' h0'] at h1
  have h2 : actO S T g 1 (actO S T g⁻¹ 1 u) = u := by
    simp only [actO, inv_inv, GlobalTheory.MixModel.mt_one, Matrix.one_mul, Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul_inv,
      Matrix.mul_one]
  rw [h2] at h1
  exact h1.symm

end PositivityTheory.Rg.Rsw.L.LWMaj

end
