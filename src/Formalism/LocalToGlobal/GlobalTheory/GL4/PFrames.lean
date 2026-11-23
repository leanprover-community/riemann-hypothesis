module

public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrCore
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  refine ⟨Submodule.fg_of_fg_map_injective f hf hmfg, ?_⟩
  intro s hs hli
  let g : W →ₗ[E] W := ((T : E) • LinearMap.id)
  have hg : Function.Injective g := smul_right_injective W (by exact_mod_cast hT : (T : E) ≠ 0)
  have hgs : g '' s ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    have hxB : x ∈ B := hs hx
    have hmul := hTB x hxB
    simpa [g, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hmul
  have hli' : LinearIndepOn (𝓞 E) id (g '' s) := by
    apply LinearIndepOn.image (f := g.restrictScalars (𝓞 E)) hli
    simp [LinearMap.ker_eq_bot.mpr hg]
  have hli'' : LinearIndepOn E id (g '' s) := hA.linearIndepOn _ hgs hli'
  exact (linearIndepOn_id_imageₛ_iff (f := g) hg.injOn).mp hli''

end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
