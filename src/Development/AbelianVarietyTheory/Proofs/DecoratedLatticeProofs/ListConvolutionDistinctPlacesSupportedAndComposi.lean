module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ConvDistinct

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ι : Type) (v : ι → GlobalTheory.FinPl.Pl D) (c : ι → WO S T →₀ ℂ), Function.Injective v → (∀ i, GlobalTheory.FinPl.CombAt (· = v i) (c i)) → ∀ L : List ι, L.Nodup → GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) ∧ ∀ f, comb ψ S T (aconv (L.map c)) f = L.foldr (fun i g => comb ψ S T (c i) g) f := by
  intro D ψ S T ι v c hv hc L
  have hsupp : ∀ L : List ι, GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) := by
    intro L
    refine GlobalTheory.QFinLaw.combAt_aconv _ (L.map c) (fun e he => ?_)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun p hp => ⟨b, hb, hp.symm⟩) (hc b u hu)
  intro hL
  refine ⟨hsupp L, fun f => ?_⟩
  induction L with
  | nil => exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    rw [List.map_cons, GlobalTheory.QFinLaw.comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = v a)) (P' := fun p => ∃ b ∈ L, v b = p) ?_ (hc a x hx) (hsupp L y hy)
    rintro _ rfl ⟨b, hb, hab⟩
    exact (List.nodup_cons.1 hL).1 (hv hab ▸ hb)

end GlobalTheory.ConvDistinct
end
