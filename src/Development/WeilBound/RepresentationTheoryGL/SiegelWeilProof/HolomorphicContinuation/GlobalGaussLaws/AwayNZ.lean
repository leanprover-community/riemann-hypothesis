module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayNZ : AwayNZ := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  classical
  have hl : ∀ τ', l τ' ≠ 0 := fun τ' => lNe D ψ θ l hC.hψ hC.hθ hC.hl τ'
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let Ψ : Mx D V.rank n → ℂ := fun x =>
    evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
      gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))
  have hΨ : Ψ ∈ awayA θ V n l s τ := Submodule.subset_span ⟨1, g, hg, by simp, rfl⟩
  refine ⟨Ψ, 0, awayIn D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨ, ?_⟩
  have h0 : ∀ τ', compAt θ τ' (0 : Mx D V.rank n) = 0 := fun τ' => by
    ext i j
    simp [compAt]
  have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
    simp only [g]
    rw [if_pos]
    simp only [Matrix.zero_apply, map_zero]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin V.rank) (Fin n) _)).2 W.zero_mem
  show evalPoly _ _ * gAway V l s τ _ * g _ ≠ 0
  rw [hg0]
  simp only [evalPoly, map_one, one_mul, mul_one, gAway, h0]
  simp

end PositivityTheory.Rg.Sw.Glob
