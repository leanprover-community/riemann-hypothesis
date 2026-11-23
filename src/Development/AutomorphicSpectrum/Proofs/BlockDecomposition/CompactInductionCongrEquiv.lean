module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩

theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
