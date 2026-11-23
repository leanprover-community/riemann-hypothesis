module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWF
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWG
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section




open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

theorem fixW : IdemEx → GenK → WMaj → FixW := by
  classical
  intro _ hG hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω
  have hHaar : μ.IsAddHaarMeasure := by
    obtain ⟨_, h, -⟩ := hμ
    exact h
  obtain ⟨S1, hS1⟩ := LFixW.fixN V hψ
  obtain ⟨S2, hS2⟩ := LFixW.fixWc V hψ
  obtain ⟨S3, hS3⟩ := LFixW.unit_triv D χ hχ
  obtain ⟨S4, hS4⟩ := hG D n
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4, fun S hS e he Φ hΦ u hu => ?_⟩
  have h1 : S1 ⊆ S := fun x hx => hS (by simp [hx])
  have h2 : S2 ⊆ S := fun x hx => hS (by simp [hx])
  have h3 : S3 ⊆ S := fun x hx => hS (by simp [hx])
  have h4 : S4 ⊆ S := fun x hx => hS (by simp [hx])
  have hcont := (hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω Φ).1
  have hA : IsClosed {g : G D n | ω g Φ = Φ} := by
    have hEq : {g : G D n | ω g Φ = Φ} = ⋂ x, {g : G D n | (ω g Φ).1 x = Φ.1 x} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h x
        rw [h]
      · intro h
        exact Subtype.ext (funext h)
    rw [hEq]
    exact isClosed_iInter fun x =>
      isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have h1A : (1 : G D n) ∈ {g : G D n | ω g Φ = Φ} := by
    show ω 1 Φ = Φ
    rw [map_one]
    rfl
  have key := hS4 S h4 {g : G D n | ω g Φ = Φ} hA h1A (by
    intro g hg hcases x hx
    have hx' : ω x Φ = Φ := hx
    show ω (g * x) Φ = Φ
    rw [map_mul]
    show ω g (ω x Φ) = Φ
    rw [hx']
    rcases hcases with hN | hM | ⟨w, u', hw, hu', hu'K, rfl⟩
    · exact hS1 S h1 n θ μ ω χ hω g hg hN Φ (fun y hy => by rw [hΦ y, if_neg hy])
    · exact LFixW.fixM V hω he (hS3 S h3) hg hM Φ hΦ
    · exact hS2 S h2 e he n θ μ ω χ hω hHaar w u' hw hu' hu'K Φ hΦ)
  exact key hu

end PositivityTheory.Rg.Rsw.L

end
