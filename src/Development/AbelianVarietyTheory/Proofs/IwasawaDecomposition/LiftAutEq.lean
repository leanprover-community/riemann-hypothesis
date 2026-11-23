module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilDatumOOfRankEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem liftAutEq : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAutEq D := by
  intro hP D θ hθ ψ hψ V W χ χ' ha om hom μ 𝓕 hq Φ F hF
  obtain ⟨omO, H, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha hom
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  have hf := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
  simp only [hE] at hf
  have e' : ∀ g h, (om (g, h) Φ).1 0 = thKer ψ V W omO ⟨fun x => Φ.1 (toTWsmall V W x), hf⟩ g h := fun g h => by
    have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm
  simp only [e']
  exact (isKerSys_thKer hθ hψ (GlobalTheory.Ker.isWeak_of_datum H) H.om_cont).lift hP hθ hq hF _

end GlobalTheory.Mem.Lift
