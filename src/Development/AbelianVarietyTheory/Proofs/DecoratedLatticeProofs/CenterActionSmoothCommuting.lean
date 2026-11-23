module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentreComm

open GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : InfFam D} {V : HSp D}


variable (θ V) in
def CommOnSm (A B : (GA D V → ℂ) → (GA D V → ℂ)) : Prop := ∀ f ∈ SmFun θ V, A (B f) = B (A f)

theorem lin_sum {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {α : Type} (s : Finset α)
    (g : α → GA D V → ℂ) (hg : ∀ a ∈ s, g a ∈ SmFun θ V) : T (∑ a ∈ s, g a) = ∑ a ∈ s, T (g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using hT.smul 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (hg a (by simp)) _
      (Submodule.sum_mem _ fun b hb => hg b (by simp [hb])), ih fun b hb => hg b (by simp [hb])]

theorem comm_foldr {T : (GA D V → ℂ) → (GA D V → ℂ)} {α : Type} (A : α → (GA D V → ℂ) → (GA D V → ℂ))
    (l : List α) (hl : ∀ a ∈ l, LinOnSm θ V (A a)) (hc : ∀ a ∈ l, CommOnSm θ V T (A a)) :
    CommOnSm θ V T fun f => l.foldr (fun a g => A a g) f := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro f hf
    have h2 := linOnSm_foldr A l fun b hb => hl b (by simp [hb])
    simp only [List.foldr_cons]
    rw [hc a (by simp) _ (h2.mem f hf), ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb])) f hf]

theorem comm_gelf {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {τ : D.what₂.Tau}
    (hc : ∀ Z, CommOnSm θ V T (RderC θ V τ Z)) (k : ℕ) : CommOnSm θ V T (gelf θ V τ k) := by
  have hl : ∀ idx : Fin (k + 1) → Fin V.rank, ∀ S ∈ (List.ofFn fun a : Fin (k + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), LinOnSm θ V S ∧ CommOnSm θ V T S := fun idx S hS => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hS
    exact ⟨linOnSm_RderC τ _, hc _⟩
  intro f hf
  simp only [gelf]
  rw [lin_sum hT _ _ fun idx _ => (linOnSm_foldr (fun S => S) _ fun S hS => (hl idx S hS).1).mem f hf]
  exact Finset.sum_congr rfl fun idx _ =>
    comm_foldr (fun S => S) _ (fun S hS => (hl idx S hS).1) (fun S hS => (hl idx S hS).2) f hf

theorem gelf_RderC (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k : ℕ) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    CommOnSm θ V (gelf θ V τ k) (RderC θ V τ' Z) := by
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  simp only [RderC]
  rw [(linOnSm_gelf τ k).add _ (Rder_mem hf h1) _ (Submodule.smul_mem _ _ (Rder_mem hf h2)), (linOnSm_gelf τ k).smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 hf, GlobalTheory.CuspLie.gelf_Rder hθ h2 hf]

end GlobalTheory.CentreComm

end
