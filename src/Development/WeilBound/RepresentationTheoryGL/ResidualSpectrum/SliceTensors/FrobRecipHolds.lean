module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs

namespace SliceFrobeniusReciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {n : Fin c → ℕ} {h : ∑ i, n i = N} {σ' : SmIrr (GL (Fin N) k)} {W : Type} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (∀ i, GL (Fin (n i)) k) W} {ℓ : σ'.V →ₗ[ℂ] W}

def frobFun (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) :
    IndSp (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹) :=
  ⟨⟨fun g => ℓ (σ'.ρ g v), fun p g => by
      show ℓ (σ'.ρ ((p : GL (Fin N) k) * g) v) = _
      rw [map_mul, Module.End.mul_apply, hℓ p]
      simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, smul_smul, ← Units.val_mul,
        MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((σ'.smooth v).mem_nhds (by simp)) fun g hg => by
      have hg' : σ'.ρ g v = v := hg
      show _ = _
      apply Subtype.ext
      funext x
      show ℓ (σ'.ρ (x * g) v) = ℓ (σ'.ρ x v)
      rw [map_mul, Module.End.mul_apply, hg'])⟩

theorem frobFun_apply (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) (v : σ'.V) (g : GL (Fin N) k) :
    (frobFun hℓ v).1.1 g = ℓ (σ'.ρ g v) := rfl

def frobMap (hℓ : ∀ (p : parab k (stdBlocks n h)) (v : σ'.V),
      ℓ (σ'.ρ p v) = ρ (leviProj k (stdBlocks n h) p) (ℓ v)) :
    σ'.ρ.IntertwiningMap (parInd (stdBlocks n h) (twist ρ (deltaHalf k fun i => Fin (n i))⁻¹)) where
  toLinearMap :=
    { toFun := frobFun hℓ
      map_add' := fun v v' => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (v + v')) = ℓ (σ'.ρ g v) + ℓ (σ'.ρ g v')
        simp))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (funext fun g => by
        show ℓ (σ'.ρ g (a • v)) = a • ℓ (σ'.ρ g v)
        simp)) }
  isIntertwining' g := by
    ext v x
    show ℓ (σ'.ρ x (σ'.ρ g v)) = ℓ (σ'.ρ (x * g) v)
    rw [map_mul, Module.End.mul_apply]

end SliceFrobeniusReciprocity

open SliceFrobeniusReciprocity in
theorem frobRecip_holds : PositivityTheory.RSHS.LS.FrobRecip := by
  intro k _ _ _ _ N c n h σ' W _ _ ρ ℓ hℓ0 hℓ
  refine ⟨frobMap hℓ, fun h0 => hℓ0 (LinearMap.ext fun v => ?_)⟩
  have h1 := congrArg (fun f : _ →ₗ[ℂ] _ => (f v).1.1 1) h0
  simpa [frobMap, frobFun_apply] using h1

end PositivityTheory.Rg.Rs

end
