module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem ph_tensInt_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  intro F E _ _ _ _ _ n p G A hA v
  have h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y := by
    intro y
    show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y
    rw [hA v y]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v) := by
      refine (Subring.closure_le).2 ?_
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · obtain ⟨r, rfl⟩ := hx
        show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F
        have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r) := (RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)
        obtain ⟨q, hq, hev⟩ := h0
        let f : E →+* (A.pl v).1.adicCompletion F := (A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)
        have hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) := rfl
        have hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))) := by
          refine ⟨q.map (Int.castRingHom _), hq.map _, ?_⟩
          rw [Polynomial.eval₂_map, ← hf]
          have := congrArg f hev
          rw [map_zero, Polynomial.hom_eval₂] at this
          have e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp
              (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
          rw [e]
          exact this
        obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
        rw [← hz]
        exact z.2
      · show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F
        rw [h1]
        exact hy
    exact hle hs
  · intro x hx
    refine ⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩
    exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end GlobalTheory.TwV
