module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.PeriodIntegrals.VolFromSW

@[expose] public section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem inclR_comp_sigma :
    (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).comp (σ : E →+* E) = (sigR (AF F) σ).comp (inclR (F := F) (AF F)) := by
  ext e
  simp [inclR, sigR]

def ratEl (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HFinIn (AF F) σ J :=
  ⟨⟨Formalism.UG.bc (inclR (F := F) (AF F)) g, Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sigma σ) J g hg⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

def GamA : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

def ratElA (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (ratEl σ J g hg : HR (AF F) σ J)

theorem ratElA_mem (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    ratElA σ J g hg ∈ GamA σ J := (ratEl σ J g hg).2

theorem ratElA_smul (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) {a : ℕ}
    (X : Fin a → Fin M → E) :
    ratElA σ J g hg • ratTup (F := F) (AF F) X =
      ratTup (F := F) (AF F) (fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X i)) := by
  funext i j
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (g : Matrix (Fin M) (Fin M) E) (X i) j).symm

instance nontrivAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

theorem ratTup_injective {a : ℕ} : Function.Injective (ratTup (F := F) (E := E) (M := M) (n := a) (AF F)) := by
  intro X X' h
  funext i j
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    (congrFun (congrFun h i) j)

end Inst

end PI.VolStabS
