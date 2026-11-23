module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  intro O K _ _ _ _ _ _ _ r
  refine ⟨fun L => ?_, fun g L => (glMap_isLattice g L).toIsLattice⟩
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
  have hr : Module.finrank O L.1 = r := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K L.1).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin r) O L.1 := Module.finBasisOfFinrankEq O L.1 hr
  let c : Module.Basis (Fin r) K (Fin r → K) := b.extendOfIsLattice K
  have hc : ∀ i, c i = (b i : Fin r → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  have he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i := fun i => by
    simpa using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)
  let g : GL (Fin r) K :=
    ⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)),
      LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)),
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K)) :=
    Matrix.toLin'_toMatrix' _
  refine ⟨g, ?_⟩
  have h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  change (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
    ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1
  rw [hg, Submodule.map_span, ← Set.range_comp]
  have h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r))
      = Subtype.val ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [he, hc]
  rw [h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.LatHecke
