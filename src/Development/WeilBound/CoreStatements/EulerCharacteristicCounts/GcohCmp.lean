module

import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem gcRep : SgcRep := by
  intro G _ _ _ R _ M _ _ _ _ rho hrho
  letI : Module (ULift.{0} ℤ) M := Module.compHom M (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let σ : Representation (ULift.{0} ℤ) G M :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add _
          map_smul' := fun c m => map_zsmul (rho g) c.down m }
      map_one' := LinearMap.ext fun m => by
        change rho 1 m = m
        rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => by
        change rho (g * h) m = rho g (rho h m)
        rw [map_mul]; rfl }
  refine ⟨Rep.of σ, ⟨fun a => ?_⟩, AddEquiv.refl M, fun g m => rfl⟩
  have hc : Continuous fun g : G => rho g (a : M) :=
    hrho.comp (continuous_id.prodMk continuous_const)
  exact (isOpen_discrete {(a : M)}).preimage hc

attribute [local instance 2000] Rep.hV2

section

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (A : Rep.{0} k G) (e : M ≃+ A.V)

omit [IsTopologicalGroup G] in
theorem lc_of_cont {X : Type} [TopologicalSpace X] {f : X → M} (hf : Continuous f) :
    IsLocallyConstant fun s => e (f s) :=
  ((IsLocallyConstant.iff_continuous f).2 hf).comp e

omit [IsTopologicalGroup G] in
theorem cont_of_lc {X : Type} [TopologicalSpace X] {f : X → A.V} (hf : IsLocallyConstant f) :
    Continuous fun s => e.symm (f s) :=
  (hf.comp e.symm).continuous

end

theorem gcn : Sgcn := by
  apply CompanionTheory.LocalTateOrthogonality.Gcoh.gcn <;> assumption

theorem gc0 : Sgc0 := by
  apply CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 <;> assumption

theorem gc1 : Sgc1 := by
  apply CompanionTheory.LocalTateOrthogonality.Gcoh.gc1 <;> assumption

theorem gc2 : Sgc2 := by
  apply CompanionTheory.LocalTateOrthogonality.Gcoh.gc2 <;> assumption

end PositivityTheory.LocalTateOrthogonality.Gcoh
