module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.LatFwd

theorem finM_inv_eq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    have e2 : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [e1, e1, ← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm

theorem proj_mem_stabLoc_std {D : D7} (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hM : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v)
    (hM' : ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g⁻¹)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.stdLattice D.host.E V.rank) v := by
  rw [map_inv, map_inv] at hM'
  set M := GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)
  have hint : ∀ (N : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)),
      (∀ i j, N i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ i, z i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) → ∀ i, (N *ᵥ z) i ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v :=
    fun N hN z hz i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hz j)
  refine GlobalTheory.AdelicU.mem_stabLoc.2 fun z => ?_
  simp only [GlobalTheory.AdelicU.mem_latLoc_stdLattice]
  refine ⟨fun hz => hint _ hM z hz, fun hz => ?_⟩
  have e : (M⁻¹).1 *ᵥ (M.1 *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e]
  exact hint _ hM' _ hz

end GlobalTheory.FamTrace.LatFwd

namespace GlobalTheory.FamTrace.LatFwd


end GlobalTheory.FamTrace.LatFwd

end
