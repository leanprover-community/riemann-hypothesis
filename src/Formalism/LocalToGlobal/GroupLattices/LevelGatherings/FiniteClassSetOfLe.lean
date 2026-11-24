module

public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CompletionIntegersIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

theorem finite_classSet_of_le {G : Type} [Group G] (Γ K K' : Subgroup G) (h : K ≤ K') [Finite (ClassSet Γ K)] :
    Finite (ClassSet Γ K') := by
  refine Finite.of_surjective (fun q : ClassSet Γ K => Quotient.liftOn' q
    (fun g => (Quotient.mk'' g : ClassSet Γ K')) (fun a b hab => ?_)) ?_
  · obtain ⟨x, hx, y, hy, rfl⟩ := (DoubleCoset.rel_iff).mp hab
    exact Quotient.sound' ((DoubleCoset.rel_iff).mpr ⟨x, hx, y, h hy, rfl⟩)
  · intro q
    exact Quotient.inductionOn' q (fun g => ⟨Quotient.mk'' g, rfl⟩)

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem U_le_awayP (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : L.U ≤ Formalism.L2.Herm.awayFrom₂ L p := by
  intro x hx
  obtain ⟨h1, h2⟩ := (L.U_eq x).mp hx
  simp only [Formalism.L2.Herm.awayFrom₂, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact ⟨h1, fun v _ => h2 v⟩

theorem finite_classSet_U (L : ColLevel R F E sp gp C A clsLat) :
    Finite (ClassSet ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))) := by
  haveI := C.clsFin 0
  exact Finite.of_surjective _ L.y_bij.2

instance finite_compL (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Finite (compL L p) := by
  have := finite_classSet_U L
  refine finite_classSet_of_le _ (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))) _ ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (U_le_awayP L p (Subgroup.mem_subgroupOf.1 hx))

end Formalism.L2.G
