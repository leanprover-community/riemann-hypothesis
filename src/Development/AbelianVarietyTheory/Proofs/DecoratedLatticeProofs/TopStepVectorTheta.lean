module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopConv

variable {D : D7}

theorem exists_finComb_of_mem_span (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {f g : WO S T → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    ∃ b : WO S T →₀ ℂ, IsFinComb b ∧ comb ψ S T b f = g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Finsupp.single a.1 1, fun u hu => ?_, by rw [GlobalTheory.StepComb.comb_single', one_smul]⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
    exact a.2
  | zero => exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), GlobalTheory.StepComb.comb_zero' ψ f⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨b + b', fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (hb u) (hb' u),
      GlobalTheory.StepComb.comb_add' ψ b b' f⟩
  | smul a x _ hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a • b, fun u hu => hb u (Finsupp.support_smul hu), GlobalTheory.StepComb.comb_smul' ψ a b f⟩

theorem isFinComb_comp (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b b' : WO S T →₀ ℂ} (hb : IsFinComb b)
    (hb' : IsFinComb b') : ∃ c : WO S T →₀ ℂ, IsFinComb c ∧ ∀ f, comb ψ S T c f = comb ψ S T b (comb ψ S T b' f) := by
  obtain ⟨c, h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 b b'
  refine ⟨c, fun w hw => ?_, h2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := h1 w hw
  ext i j
  have e1 := congrFun (congrFun (hb x hx) i) j
  have e2 := congrFun (congrFun (hb' y hy) i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at e1 e2 ⊢
  rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e2, add_zero]

end GlobalTheory.TopConv

end

noncomputable section

namespace GlobalTheory.TopConv

theorem comb_mem_span {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b : WO S T →₀ ℂ} (hb : IsFinComb b)
    (f : WO S T → ℂ) :
    comb ψ S T b f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  unfold comb
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hb u hu⟩, rfl⟩)


end GlobalTheory.TopConv

end
